/**
 * Which mount points on the host a running sandbox still relies on (Linux).
 *
 * A deny on a path that does not exist needs a mount point there: bwrap makes
 * an empty file or directory on the host and binds over it. Unlinking it while
 * a sandbox is bound over it detaches the mount inside that sandbox, and the
 * denied path can then be created on the host. So a mount point may be removed
 * only when no running sandbox relies on it, and no process can decide that by
 * counting for itself.
 *
 * The kernel is asked instead. Each wrap writes a manifest naming its mount
 * points into a per-user directory and passes `--lock-file <manifest>` to
 * bwrap, whose sandbox init process holds a read lock on it for the sandbox's
 * lifetime; the kernel drops it however the sandbox ends. /proc/locks then
 * tells any process whether a sandbox that named a mount point is running, so
 * cleanup is a garbage collect any process may run at any time.
 *
 * Two processes of one user keep each other's mount points only when each reads
 * what the other writes, so where the manifests go is worked out from the user
 * id and the file system before the environment, which differs between a login
 * shell and what a service, an IDE or cron starts (see {@link
 * manifestDirectoryCandidates}). A process writes to the first of those
 * directories it can use and believes what it finds in the ones that come from
 * the user id, or, where it can use none of those, in the ones its environment
 * names (see {@link believedManifestDirectories}).
 *
 * Every one of them is bound read-only into every sandbox that restricts
 * writes, and is made first if it is missing, and the directories above it
 * inside a write root are pinned, so a sandboxed command can neither rewrite a
 * manifest nor make or swap the directory (see {@link
 * mountPointManifestDirectories}). Not covered: a sandbox this library did not
 * start, the sandbox of a process with another environment where a process has
 * to keep its manifests under a name its own environment gives, and a directory
 * whose name, or a name above it, is a link inside a write root or whose parent
 * is not there yet.
 *
 * /proc/locks and /proc/PID are relative to a PID namespace, so a manifest
 * records the namespace that wrote it and only a process in that namespace
 * judges it; to any other it is live.
 */

import { randomBytes } from 'node:crypto'
import * as fs from 'node:fs'
import { tmpdir } from 'node:os'
import path from 'node:path'
import { z } from 'zod'
import { logForDebugging } from '../utils/debug.js'
import { isAbsenceErrno } from './sandbox-utils.js'

/** The only manifest layout this version writes and reads. */
const MANIFEST_VERSION = 1
const MANIFEST_SUFFIX = '.json'

/**
 * A manifest this young counts as live with no lock on it. bubblewrap takes the
 * lock a few milliseconds after the wrap returns; a wrapping process killed in
 * between must not leave a starting sandbox's mount point unclaimed.
 */
const MANIFEST_GRACE_MS = 500

/** How long a collect or a publish waits for the directory lock. */
const DIRECTORY_LOCK_WAIT_MS = 2_000

/** Between attempts at the directory lock. */
const DIRECTORY_LOCK_RETRY_MS = 25

/**
 * A directory lock this old is broken whoever holds it: the only way out for a
 * holder that cannot be asked after (another PID namespace, unreadable
 * content). A holder that is gone is broken at once.
 */
const DIRECTORY_LOCK_STALE_MS = 60_000

/**
 * How many mount points a pass removes on one read of /proc/locks, and for how
 * long one read is good. A sandbox needs several milliseconds from its manifest
 * being published to its binds being in place, so both stay under that; one
 * read per removal would make a pass on a busy host outlast the directory lock
 * wait.
 */
const REMOVALS_PER_LOOK = 64
const LOCKS_GOOD_FOR_MS = 2

/**
 * For how long one listing of the manifest directory is good: well under the
 * time a starting sandbox needs to reach its binds, and a time rather than
 * "before every removal" so a directory of thousands is not listed thousands of
 * times.
 */
const LISTING_GOOD_FOR_MS = 0.25

/**
 * An unreadable manifest with no lock on it is dropped once it is this old:
 * long enough for another version of this library to keep its own format.
 */
const UNREADABLE_MANIFEST_MAX_AGE_MS = 60 * 60 * 1000

/** The largest file read as a manifest; a real one is a few kilobytes. */
const MANIFEST_MAX_BYTES = 1024 * 1024

/**
 * Suffix of a manifest or directory lock before it is moved into place. One
 * left by a killed process is removed at {@link
 * UNREADABLE_MANIFEST_MAX_AGE_MS}.
 */
const TEMPORARY_SUFFIX = '.tmp'

const ManifestSchema = z.object({
  version: z.literal(MANIFEST_VERSION),
  /** The process that wrapped, and its start time, to tell a recycled pid. */
  pid: z.number().int().nonnegative(),
  start: z.string(),
  /**
   * The writer's PID namespace (`readlink /proc/self/ns/pid`): `pid` and the
   * lock can only be asked after from there. Absent in older manifests.
   */
  ns: z.string().optional(),
  /** When the manifest was written, for {@link MANIFEST_GRACE_MS}. */
  created: z.number(),
  /** The mount points bwrap makes on the host for that wrap's deny paths. */
  paths: z.array(z.string()),
  /**
   * The empty directories those mount points bind from. A live bind's source
   * must stay, so they are collected the same way (see {@link
   * removeMountSource}).
   */
  sources: z.array(z.string()),
})

type Manifest = z.infer<typeof ManifestSchema> & {
  file: string
  /** The inode /proc/locks reports a lock on, and the device it is on. */
  inode: string
  device: string
  /**
   * This process wrote it, the caller says the command is over, and nothing
   * held the lock when the pass began: only a lock can still make it live.
   */
  released: boolean
}

/**
 * Manifests this process wrote that are still on disk, with the command key the
 * caller gave and whether that command is over. Remembered rather than acted on
 * at once: a manifest must stay on disk until a pass removes what it names.
 */
const ownManifests = new Map<
  string,
  { commandKey: string | undefined; over: boolean }
>()

/**
 * Which of this process's own manifests a collect may release. Only the caller
 * knows that a command is over:
 *
 * - `all`: no wrap of this process is outstanding, or the process is ending;
 * - `none`: some are, and nothing says which is over, so only what other
 *   processes have finished with is collected;
 * - one command: that command is over, whatever else is running.
 *
 * Never release the manifest of a wrap whose command has not started:
 * bubblewrap opens the manifest to lock it, and the command would refuse to
 * start or run with nothing on disk naming its mount points.
 */
export type OwnManifestRelease = 'all' | 'none' | { commandKey: string }

let manifestDirectory: string | undefined
// Whether that is the last resort below, which no other process knows of.
let manifestDirectoryIsPrivate = false
let directoryFailureLogged = false
// Set once the last resort has been tried and found wanting, so a process on a
// temp dir that keeps no modes does not make a fresh directory on every call.
let manifestDirectoryUnavailable = false

/** Everything here is for bubblewrap, which is Linux's. */
const onLinux = (): boolean => process.platform === 'linux'

/**
 * Field 22 of /proc/PID/stat, the start time in clock ticks, counted from the
 * last ')' because the comm field can hold spaces and parentheses.
 */
function startTimeFromProcStat(stat: string): string | undefined {
  return stat
    .slice(stat.lastIndexOf(')') + 1)
    .trim()
    .split(' ')[19]
}

function processStartTime(pid: number): string | undefined {
  try {
    return startTimeFromProcStat(fs.readFileSync(`/proc/${pid}/stat`, 'utf8'))
  } catch {
    return undefined
  }
}

/**
 * Whether the process a manifest names is still running. An unreadable /proc
 * answers yes: it must not make a live sandbox's manifest collectable.
 */
function writerIsRunning(pid: number, start: string): boolean {
  try {
    return (
      startTimeFromProcStat(fs.readFileSync(`/proc/${pid}/stat`, 'utf8')) ===
      start
    )
  } catch (e) {
    return !isAbsenceErrno(e)
  }
}

let pidNamespace: string | undefined | null = null

/** This process's PID namespace as the kernel names it, or `undefined`. */
function ownPidNamespace(): string | undefined {
  if (pidNamespace === null) {
    try {
      pidNamespace = fs.readlinkSync('/proc/self/ns/pid')
    } catch {
      pidNamespace = undefined
    }
  }
  return pidNamespace
}

/** `major:minor` in decimal, as /proc/locks prints a device. */
function deviceOf(dev: bigint): string {
  const major = ((dev >> 8n) & 0xfffn) | ((dev >> 32n) & ~0xfffn)
  const minor = (dev & 0xffn) | ((dev >> 12n) & ~0xffn)
  return `${major}:${minor}`
}

/**
 * Filesystems on which stat reports the device /proc/locks prints. Elsewhere (a
 * btrfs subvolume, some overlays) only the inode number can be compared.
 */
const FILESYSTEMS_WITH_ONE_DEVICE = new Set([
  0x01021994, // tmpfs, which is what /run/user/UID is
  0xef53, // ext2, ext3, ext4
  0x58465342, // xfs
])

function reportsTheLockedDevice(dir: string): boolean {
  try {
    return FILESYSTEMS_WITH_ONE_DEVICE.has(Number(fs.statfsSync(dir).type))
  } catch {
    return false
  }
}

/** The locks /proc/locks lists, of any kind, by what they are on. */
type Locks = {
  /** Every inode number with a lock on it, whatever filesystem it is on. */
  inodes: Set<string>
  /** The same locks as `major:minor:inode`, in decimal. */
  files: Set<string>
  /** The directories whose manifests' device can be held against `files`. */
  comparesDevices: Set<string>
}

/**
 * Whether /proc/locks lists a lock on this file; nothing but bubblewrap's
 * sandbox init locks a manifest. The device is compared where it can be: inode
 * numbers are per filesystem, and an unrelated locked file with the same number
 * would otherwise keep a manifest live. Where it cannot, the inode alone
 * decides, which errs towards "locked".
 */
function holdsLock(
  locks: Locks,
  file: { file: string; inode: string; device: string },
): boolean {
  return locks.comparesDevices.has(path.dirname(file.file))
    ? locks.files.has(`${file.device}:${file.inode}`)
    : locks.inodes.has(file.inode)
}

/**
 * What /proc/locks lists. Only locks whose holder has a pid in this PID
 * namespace appear. `undefined` when it cannot be read, which every caller
 * treats as "every manifest is locked".
 */
function readLocks(dirs: readonly string[]): Locks | undefined {
  let text: string
  try {
    text = fs.readFileSync('/proc/locks', 'utf8')
  } catch (e) {
    logForDebugging(
      `[Sandbox Linux] /proc/locks could not be read (${String(e)}) - leaving every mount point where it is`,
      { level: 'warn' },
    )
    return undefined
  }
  const inodes = new Set<string>()
  const files = new Set<string>()
  for (const line of text.split('\n')) {
    // The major:minor:inode word, which sits one field later on the lines that
    // describe a blocked request ("2: -> POSIX ADVISORY WRITE ...").
    for (const word of line.split(/\s+/)) {
      const match = /^([0-9a-f]+):([0-9a-f]+):(\d+)$/.exec(word)
      if (match !== null) {
        const inode = String(BigInt(match[3]!))
        inodes.add(inode)
        files.add(
          `${parseInt(match[1]!, 16)}:${parseInt(match[2]!, 16)}:${inode}`,
        )
        break
      }
    }
  }
  return {
    inodes,
    files,
    comparesDevices: new Set(dirs.filter(reportsTheLockedDevice)),
  }
}

/** Whether `dir` is a directory of ours that nobody else can write, and we can. */
function isOurPrivateDirectory(dir: string): boolean {
  try {
    const stat = fs.lstatSync(dir)
    if (
      !stat.isDirectory() ||
      stat.uid !== process.getuid?.() ||
      (stat.mode & 0o077) !== 0
    ) {
      return false
    }
    // Ours, and no use if it cannot be written: a directory an outer sandbox
    // binds read-only reads as ours in every other respect.
    fs.accessSync(dir, fs.constants.W_OK | fs.constants.X_OK)
    return true
  } catch {
    return false
  }
}

/**
 * Make `dir` a directory of ours alone, or say it cannot be. The name is
 * predictable and sandboxed commands can often write beside it, so it is opened
 * without following a link and its mode is set on the descriptor: a symlink
 * planted at the name is refused, not followed.
 */
function makeOurPrivateDirectory(dir: string): boolean {
  try {
    fs.mkdirSync(dir, { mode: 0o700 })
  } catch {
    // There already, or cannot be made: the look below decides.
  }
  let fd: number | undefined
  try {
    fd = fs.openSync(
      dir,
      fs.constants.O_RDONLY |
        fs.constants.O_DIRECTORY |
        fs.constants.O_NOFOLLOW,
    )
    const stat = fs.fstatSync(fd)
    if (!stat.isDirectory() || stat.uid !== process.getuid?.()) {
      return false
    }
    // mkdir asks for 0700 but the umask applies, and a directory an earlier
    // run left keeps the mode it was made with.
    if ((stat.mode & 0o777) !== 0o700) {
      fs.fchmodSync(fd, 0o700)
    }
  } catch {
    return false
  } finally {
    if (fd !== undefined) fs.closeSync(fd)
  }
  return isOurPrivateDirectory(dir)
}

/**
 * Whether bubblewrap could not reach a manifest under `dir`: the wrap mounts a
 * fresh /dev and /proc over whatever was bound beneath them.
 */
function isBuriedBySandboxMounts(dir: string): boolean {
  return ['/dev', '/proc', '/sys'].some(
    root => dir === root || dir.startsWith(`${root}/`),
  )
}

/**
 * The places the manifest directories are looked for in. The first two are the
 * same for every process of a user; the last two are what this process's
 * environment says.
 */
export type ManifestDirectoryPlaces = {
  /** The user's runtime directory where the system keeps one: /run/user/UID. */
  runtimeDir: string
  /** The temp dir every process can name: /tmp. */
  tempDir: string
  /** $XDG_RUNTIME_DIR, where it is set. */
  environmentRuntimeDir: string | undefined
  /** The system temp dir as this process sees it, which is $TMPDIR's. */
  environmentTempDir: string
}

// What a test has put in the place of some of those, and nothing else has.
let placesForTesting: Partial<ManifestDirectoryPlaces> | undefined

function manifestDirectoryPlaces(): ManifestDirectoryPlaces {
  return {
    runtimeDir: `/run/user/${process.getuid?.() ?? 0}`,
    tempDir: '/tmp',
    environmentRuntimeDir: process.env['XDG_RUNTIME_DIR'],
    environmentTempDir: tmpdir(),
    ...placesForTesting,
  }
}

/**
 * Whether `dir` is a runtime directory of this user's as the system makes one:
 * a real directory, not a link, the user's, and closed to everyone else.
 */
function isTheUsersRuntimeDirectory(dir: string): boolean {
  try {
    const stat = fs.lstatSync(dir)
    return (
      stat.isDirectory() &&
      stat.uid === process.getuid?.() &&
      (stat.mode & 0o077) === 0
    )
  } catch {
    return false
  }
}

/**
 * Where the directory `name` names really is, as far as can be told before it
 * is made: its parent with links resolved, plus its own last component.
 */
function whereItReallyIs(name: string): string {
  try {
    return path.join(fs.realpathSync(path.dirname(name)), path.basename(name))
  } catch {
    return path.resolve(name)
  }
}

/**
 * The names under which processes of this user keep manifests that others can
 * find, in the order tried for writing:
 *
 * - `/run/user/UID/srt-mount-points`, where `/run/user/UID` is a runtime
 *   directory of the user's (see {@link isTheUsersRuntimeDirectory});
 * - `/tmp/srt-mount-points-UID`;
 * - `$XDG_RUNTIME_DIR/srt-mount-points`, where that is set;
 * - `srt-mount-points-UID` under the system temp dir, which is `$TMPDIR`'s.
 *
 * The user id and the file system come first because they are the same for
 * every process of the user. The environment is not: two processes that each
 * wrote where their own environment said would never read each other's
 * manifests, and one would remove the other's mount point from under its
 * sandbox. The names from the environment stay, last, for a process that can
 * use neither of the first two. Two names for one directory count once, and one
 * that a sandbox's own mounts would bury is left out.
 */
function manifestDirectoryCandidates(): {
  name: string
  fromTheEnvironment: boolean
}[] {
  const places = manifestDirectoryPlaces()
  const perUser = `srt-mount-points-${process.getuid?.() ?? 0}`
  const names: { name: string; fromTheEnvironment: boolean }[] = []
  if (isTheUsersRuntimeDirectory(places.runtimeDir)) {
    names.push({
      name: path.join(places.runtimeDir, 'srt-mount-points'),
      fromTheEnvironment: false,
    })
  }
  names.push({
    name: path.join(places.tempDir, perUser),
    fromTheEnvironment: false,
  })
  if (
    places.environmentRuntimeDir !== undefined &&
    path.isAbsolute(places.environmentRuntimeDir)
  ) {
    names.push({
      name: path.join(places.environmentRuntimeDir, 'srt-mount-points'),
      fromTheEnvironment: true,
    })
  }
  names.push({
    name: path.join(places.environmentTempDir, perUser),
    fromTheEnvironment: true,
  })
  const found = new Set<string>()
  return names.filter(candidate => {
    const where = whereItReallyIs(candidate.name)
    if (isBuriedBySandboxMounts(candidate.name) || found.has(where)) {
      return false
    }
    found.add(where)
    return true
  })
}

/** The names of {@link manifestDirectoryCandidates}, in their order. */
function sharedManifestDirectoryNames(): string[] {
  return manifestDirectoryCandidates().map(candidate => candidate.name)
}

/**
 * The directory this process writes its manifests to: the first shared name
 * (see {@link sharedManifestDirectoryNames}) that can be made ours alone, else
 * a private directory only this process knows, which keeps the guarantee within
 * this process. Revalidated on every use, because a directory swapped for a
 * symlink between two wraps would send manifests elsewhere.
 */
function ensureManifestDirectory(): string | undefined {
  if (
    manifestDirectory !== undefined &&
    isOurPrivateDirectory(manifestDirectory)
  ) {
    return manifestDirectory
  }
  manifestDirectoryIsPrivate = false
  for (const candidate of sharedManifestDirectoryNames()) {
    if (makeOurPrivateDirectory(candidate)) {
      manifestDirectory = candidate
      return candidate
    }
  }
  manifestDirectory = undefined
  const systemTempDir = manifestDirectoryPlaces().environmentTempDir
  if (manifestDirectoryUnavailable || isBuriedBySandboxMounts(systemTempDir)) {
    return undefined
  }
  try {
    const private_ = fs.mkdtempSync(
      path.join(systemTempDir, 'srt-mount-points-'),
    )
    if (!makeOurPrivateDirectory(private_)) {
      // A temp dir that keeps no modes or ownership: nothing made in it can be
      // told from somebody else's, now or on the next call.
      try {
        fs.rmdirSync(private_)
      } catch {
        // Left; it is empty.
      }
      throw new Error(`${private_} cannot be made private`)
    }
    manifestDirectory = private_
    manifestDirectoryIsPrivate = true
    logForDebugging(
      `[Sandbox Linux] No shared directory for mount point manifests, using one only this process knows: ${private_}`,
      { level: 'warn' },
    )
    return private_
  } catch (e) {
    manifestDirectoryUnavailable = true
    if (!directoryFailureLogged) {
      directoryFailureLogged = true
      logForDebugging(
        `[Sandbox Linux] No directory for mount point manifests (${String(e)}) - the mount points this process makes are left on the host`,
        { level: 'warn' },
      )
    }
    return undefined
  }
}

/** Whether `dir` is a real directory, not a link to one, and the user's. */
function isOurDirectory(dir: string): boolean {
  try {
    const stat = fs.lstatSync(dir)
    return stat.isDirectory() && stat.uid === process.getuid?.()
  } catch {
    return false
  }
}

/**
 * Every directory whose manifests this process believes, for a wrap, a clean-up
 * and {@link liveMountPoints} to read:
 *
 * - each name that comes from the user id that is there and is a directory of
 *   ours alone that we can write;
 * - the names the environment gives, held to the same, only where none of the
 *   first kind will do;
 * - the one this process has settled on.
 *
 * What the environment names is kept out of a sandboxed command's reach only by
 * processes whose environment names it; a command of a process with another
 * temp dir may write there. A manifest planted that way must not keep or remove
 * a path, so such a directory is believed only by a process that has nowhere
 * else to keep its own. One that is a link, somebody else's, open to others or
 * not writable is passed over. Nothing is made.
 */
function believedManifestDirectories(): string[] {
  const usable = manifestDirectoryCandidates().filter(candidate =>
    isOurPrivateDirectory(candidate.name),
  )
  const fromTheUserId = usable.filter(
    candidate => !candidate.fromTheEnvironment,
  )
  const dirs = (fromTheUserId.length > 0 ? fromTheUserId : usable).map(
    candidate => candidate.name,
  )
  if (
    manifestDirectory !== undefined &&
    !dirs.includes(manifestDirectory) &&
    isOurPrivateDirectory(manifestDirectory)
  ) {
    dirs.push(manifestDirectory)
  }
  return dirs
}

/**
 * Every directory a wrap must bind read-only because some process of this user
 * keeps manifests in it and a collect believes what it finds there: every
 * shared name, plus the one this process settled on.
 *
 * Every name, not only the one this process writes to: a sandbox with the temp
 * dir writable could otherwise forge manifests in the directory under it while
 * its own process writes under the runtime directory. Each is made if it can
 * be, so a sandboxed command cannot make and fill it first: the command runs as
 * the user, so what it makes passes every check of owner and mode. One that is
 * there and the user's is listed even when it cannot be written from here. With
 * `recording`, the directory this wrap's manifest will go to is settled first,
 * so the wrap can pin what lies above it before it publishes.
 */
export function mountPointManifestDirectories(recording = false): string[] {
  if (!onLinux()) {
    return []
  }
  const dirs = new Set<string>()
  for (const candidate of sharedManifestDirectoryNames()) {
    makeOurPrivateDirectory(candidate)
    if (isOurDirectory(candidate)) {
      dirs.add(candidate)
    }
  }
  if (recording) {
    ensureManifestDirectory()
  }
  if (manifestDirectory !== undefined && isOurDirectory(manifestDirectory)) {
    dirs.add(manifestDirectory)
  }
  return [...dirs]
}

/**
 * Remove the directory only this process knows, once it is empty, when the
 * process or its session ends. It stays while a manifest is in it.
 */
export function removePrivateManifestDirectory(): void {
  if (manifestDirectory === undefined || !manifestDirectoryIsPrivate) {
    return
  }
  try {
    fs.rmdirSync(manifestDirectory)
  } catch {
    // Not empty, or gone already.
    return
  }
  manifestDirectory = undefined
  manifestDirectoryIsPrivate = false
}

/** Block this thread, the only sleep available to a synchronous cleanup. */
function sleep(ms: number): void {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms)
}

/** What the directory lock holds: who took it, and in which PID namespace. */
function directoryLockContent(): string {
  return `${process.pid} ${processStartTime(process.pid) ?? '?'} ${ownPidNamespace() ?? '?'}\n`
}

/**
 * Take the directory lock: returns what it now holds, `held` when the name is
 * taken, or `unavailable` when this process cannot make one there. The content
 * is written under another name and hard-linked into place, so a waiter never
 * reads a lock that is still empty and takes it for abandoned.
 */
function takeDirectoryLock(
  dir: string,
  lockFile: string,
): { content: string } | 'held' | 'unavailable' {
  const content = directoryLockContent()
  const temporary = path.join(
    dir,
    `directory.lock.${process.pid}.${randomBytes(8).toString('hex')}${TEMPORARY_SUFFIX}`,
  )
  try {
    fs.writeFileSync(temporary, content, { mode: 0o600, flag: 'wx' })
  } catch {
    return 'unavailable'
  }
  try {
    fs.linkSync(temporary, lockFile)
    return { content }
  } catch (e) {
    return (e as NodeJS.ErrnoException).code === 'EEXIST'
      ? 'held'
      : 'unavailable'
  } finally {
    try {
      fs.unlinkSync(temporary)
    } catch {
      // Gone with the directory.
    }
  }
}

/**
 * Give the directory lock up if it is still this process's. One broken for its
 * age meanwhile belongs to whoever took it next.
 */
function releaseDirectoryLock(lockFile: string, content: string): void {
  try {
    if (fs.readFileSync(lockFile, 'utf8') === content) {
      fs.unlinkSync(lockFile)
    }
  } catch {
    // Broken by another process while we held it: nothing to undo.
  }
}

/**
 * What stands at the directory lock's name once taking it has failed:
 *
 * - `free`: nothing, or the lock of a holder that is gone, now removed;
 * - `held`: somebody's lock, to be waited for;
 * - `stuck`: something this process can neither read as a lock nor remove.
 *
 * Breaking a lock is read, ask, unlink, not one step, so a slow waiter's unlink
 * can land on a lock a third process has taken since. Nothing prevents that,
 * which is why nothing rests on this lock (see {@link withDirectoryLock}).
 */
function examineDirectoryLock(lockFile: string): 'free' | 'held' | 'stuck' {
  let holder: string
  let age: number
  try {
    // Opened without blocking or following a link: opening a FIFO waits for a
    // writer, and only a regular file is a lock this library made.
    if (!fs.lstatSync(lockFile).isFile()) {
      return 'stuck'
    }
    const fd = fs.openSync(
      lockFile,
      fs.constants.O_RDONLY | fs.constants.O_NONBLOCK | fs.constants.O_NOFOLLOW,
    )
    try {
      const stat = fs.fstatSync(fd)
      if (!stat.isFile()) {
        return 'stuck'
      }
      age = Date.now() - stat.mtimeMs
      holder = fs.readFileSync(fd, 'utf8')
    } finally {
      fs.closeSync(fd)
    }
  } catch (e) {
    // Gone meanwhile: the next attempt takes it. Anything else cannot be read.
    return (e as NodeJS.ErrnoException).code === 'ENOENT' ? 'free' : 'stuck'
  }
  // A holder can be asked after only in its own PID namespace. One that cannot
  // be, or that did not say who it is, is believed until the lock is stale.
  const who = /^(\d+) (\d+) (\S+)\n$/.exec(holder)
  const held =
    age < DIRECTORY_LOCK_STALE_MS &&
    (who === null ||
      who[3] !== ownPidNamespace() ||
      writerIsRunning(Number(who[1]), who[2]!))
  if (held) {
    return 'held'
  }
  try {
    fs.unlinkSync(lockFile)
  } catch (e) {
    // Another process broke it first, or it cannot be removed from here.
    return (e as NodeJS.ErrnoException).code === 'ENOENT' ? 'free' : 'stuck'
  }
  return 'free'
}

/**
 * Run `body` while holding the manifest directory's lock, and report whether it
 * ran and, if not, whether the lock was `held` throughout. Gives up after
 * {@link DIRECTORY_LOCK_WAIT_MS}, and at once when what is at the lock's name
 * can never be taken: the wait blocks the wrap, the clean-up after every
 * command and the exit handler.
 *
 * The lock keeps srt processes out of each other's way; it does not exclude,
 * and nothing may rest on it. Its holder can outlive the age at which it is
 * broken, the break is not atomic, and a publish that cannot have the lock goes
 * ahead without it. What makes a mount point safe to remove is looked at again
 * immediately before the removals and during them (see {@link
 * collectUnderLock}).
 */
function withDirectoryLock<T>(
  dir: string,
  body: () => T,
): { ran: true; value: T } | { ran: false; held: boolean } {
  const lockFile = path.join(dir, 'directory.lock')
  const deadline = Date.now() + DIRECTORY_LOCK_WAIT_MS
  for (;;) {
    const taken = takeDirectoryLock(dir, lockFile)
    if (taken === 'unavailable') {
      return { ran: false, held: false }
    }
    if (taken !== 'held') {
      try {
        return { ran: true, value: body() }
      } finally {
        releaseDirectoryLock(lockFile, taken.content)
      }
    }
    if (examineDirectoryLock(lockFile) === 'stuck') {
      logForDebugging(
        `[Sandbox Linux] ${lockFile} is not a lock this process can take or break - going on without it`,
        { level: 'warn' },
      )
      return { ran: false, held: false }
    }
    // On every round: a lock that others keep breaking and retaking is as good
    // as held.
    if (Date.now() >= deadline) {
      return { ran: false, held: true }
    }
    sleep(DIRECTORY_LOCK_RETRY_MS)
  }
}

/**
 * What is at a manifest's name, read as one, or `undefined` when it is not a
 * manifest this version can read. Only a regular file of the user's, no larger
 * than {@link MANIFEST_MAX_BYTES}, is read, through a descriptor opened without
 * following a link and without blocking.
 */
function readManifest(file: string): Manifest | undefined {
  let inode: string
  let device: string
  let text: string
  try {
    const fd = fs.openSync(
      file,
      fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK,
    )
    try {
      const stat = fs.fstatSync(fd, { bigint: true })
      if (
        !stat.isFile() ||
        Number(stat.uid) !== process.getuid?.() ||
        stat.size > MANIFEST_MAX_BYTES
      ) {
        return undefined
      }
      inode = String(stat.ino)
      device = deviceOf(stat.dev)
      text = fs.readFileSync(fd, 'utf8')
    } finally {
      fs.closeSync(fd)
    }
  } catch {
    return undefined
  }
  let json: unknown
  try {
    json = JSON.parse(text)
  } catch {
    return undefined
  }
  const parsed = ManifestSchema.safeParse(json)
  return parsed.success
    ? { ...parsed.data, file, inode, device, released: false }
    : undefined
}

/**
 * Whether a sandbox that named this manifest may still be running, as far as
 * this process can tell. It can tell only for a manifest written in its own PID
 * namespace; one from another namespace is always live here and is collected by
 * a process in the namespace that wrote it. One that names no namespace is live
 * while its writer can be seen, and otherwise until {@link
 * UNREADABLE_MANIFEST_MAX_AGE_MS}.
 */
function isLive(manifest: Manifest, locks: Locks): boolean {
  if (holdsLock(locks, manifest)) {
    return true
  }
  if (manifest.released) {
    return false
  }
  const here = ownPidNamespace()
  if (manifest.ns === undefined || here === undefined) {
    return (
      writerIsRunning(manifest.pid, manifest.start) ||
      Date.now() - manifest.created < UNREADABLE_MANIFEST_MAX_AGE_MS
    )
  }
  if (manifest.ns !== here) {
    return true
  }
  return (
    Date.now() - manifest.created < MANIFEST_GRACE_MS ||
    writerIsRunning(manifest.pid, manifest.start)
  )
}

/**
 * What became of a path a pass set out to remove: `left` when it is gone or no
 * longer what bubblewrap or this library made, `failed` when it is still that
 * and could not be removed from here.
 */
type Removal = 'removed' | 'left' | 'failed'

/** Whether a failed removal means the path is no longer ours to remove. */
function meansNothingToRemove(e: unknown): boolean {
  const code = (e as NodeJS.ErrnoException | undefined)?.code
  // Not empty after all: something was written into it meanwhile.
  return isAbsenceErrno(e) || code === 'ENOTEMPTY' || code === 'EEXIST'
}

/**
 * Remove an empty directory a placeholder bound from, if it is still our own.
 * It sits where sandboxed commands can often write, so anything but a private
 * empty directory of ours is left exactly as found.
 */
function removeMountSource(source: string): Removal {
  try {
    const stat = fs.lstatSync(source)
    if (
      !stat.isDirectory() ||
      stat.uid !== process.getuid?.() ||
      (stat.mode & 0o077) !== 0 ||
      fs.readdirSync(source).length > 0
    ) {
      logForDebugging(
        `[Sandbox Linux] Left the empty-directory mount source behind, it is no longer our own empty directory: ${source}`,
      )
      return 'left'
    }
    fs.rmdirSync(source)
    logForDebugging(
      `[Sandbox Linux] Cleaned up the empty-directory mount source: ${source}`,
    )
    return 'removed'
  } catch (e) {
    if (meansNothingToRemove(e)) {
      return 'left'
    }
    logForDebugging(
      `[Sandbox Linux] Could not remove the empty-directory mount source (${String(e)}): ${source}`,
    )
    return 'failed'
  }
}

/**
 * Whether `p` still has the shape of a file bubblewrap made to bind onto: a
 * regular file (not a link), empty, with no write bit, under one name, and
 * ours. A manifest is only a claim about a path, so nothing is removed on its
 * word that does not also look like what bubblewrap leaves.
 */
export function isBwrapFileMountPoint(p: string): boolean {
  try {
    const stat = fs.lstatSync(p)
    return (
      stat.isFile() &&
      stat.size === 0 &&
      (stat.mode & 0o222) === 0 &&
      stat.nlink === 1 &&
      stat.uid === process.getuid?.()
    )
  } catch {
    return false
  }
}

/**
 * What kind of mount point the path a live manifest names still is, by what is
 * there now: an empty regular file, a directory, or neither any more.
 */
export function kindOfMountPoint(p: string): 'file' | 'directory' | undefined {
  try {
    const stat = fs.lstatSync(p)
    if (stat.isFile() && stat.size === 0) {
      return 'file'
    }
    return stat.isDirectory() ? 'directory' : undefined
  } catch {
    return undefined
  }
}

/**
 * Remove a mount point if it is still the empty file or directory bwrap made;
 * anything else is left where it is.
 */
function removeMountPoint(mountPoint: string): Removal {
  try {
    if (isBwrapFileMountPoint(mountPoint)) {
      fs.unlinkSync(mountPoint)
      logForDebugging(
        `[Sandbox Linux] Cleaned up bwrap mount point (file): ${mountPoint}`,
      )
      return 'removed'
    }
    const stat = fs.lstatSync(mountPoint)
    if (stat.isDirectory() && stat.uid === process.getuid?.()) {
      if (fs.readdirSync(mountPoint).length > 0) {
        logForDebugging(
          `[Sandbox Linux] Left a bwrap mount point directory behind, something has written into it: ${mountPoint}`,
        )
        return 'left'
      }
      // rmdir, not a recursive remove: it neither follows a symlink nor
      // descends, so a path that is no longer ours is left exactly as found.
      fs.rmdirSync(mountPoint)
      logForDebugging(
        `[Sandbox Linux] Cleaned up bwrap mount point (dir): ${mountPoint}`,
      )
      return 'removed'
    }
    logForDebugging(
      `[Sandbox Linux] Left a path a manifest names where it is, it no longer looks like a bwrap mount point: ${mountPoint}`,
    )
    return 'left'
  } catch (e) {
    if (meansNothingToRemove(e)) {
      return 'left'
    }
    logForDebugging(
      `[Sandbox Linux] Could not remove a bwrap mount point (${String(e)}): ${mountPoint}`,
    )
    return 'failed'
  }
}

/** What {@link publishMountPointManifest} wrote, for the bwrap invocation. */
export type MountPointManifest = {
  /** The directory to bind read-only inside the sandbox. */
  dir: string
  /** The manifest, for bubblewrap's --lock-file. */
  file: string
}

/**
 * Record the mount points this wrap relies on, and the empty directories they
 * bind from, before the sandbox can start, and say where to point bubblewrap's
 * --lock-file.
 *
 * `undefined` when there is nothing to record or no manifest could be written.
 * The caller must then not track those mount points: what this process cannot
 * record it does not remove, and nobody else will.
 */
export function publishMountPointManifest(
  mountPoints: readonly string[],
  sources: readonly string[],
  commandKey?: string,
): MountPointManifest | undefined {
  if (!onLinux() || (mountPoints.length === 0 && sources.length === 0)) {
    return undefined
  }
  const dir = ensureManifestDirectory()
  if (dir === undefined) {
    return undefined
  }
  const file = path.join(
    dir,
    `${process.pid}-${randomBytes(8).toString('hex')}${MANIFEST_SUFFIX}`,
  )
  const temporary = `${file}${TEMPORARY_SUFFIX}`
  const body: z.infer<typeof ManifestSchema> = {
    version: MANIFEST_VERSION,
    pid: process.pid,
    start: processStartTime(process.pid) ?? '',
    ns: ownPidNamespace(),
    created: Date.now(),
    paths: [...new Set(mountPoints)],
    sources: [...new Set(sources)],
  }
  // Written beside the manifest and renamed onto it, so a collect reads it
  // whole or not at all. Under the directory lock where that can be had; a wrap
  // is not refused for want of one, because every pass lists the directory
  // again before it removes anything (see collectUnderLock).
  try {
    fs.writeFileSync(temporary, JSON.stringify(body), { mode: 0o600 })
    const publish = (): void => fs.renameSync(temporary, file)
    if (!withDirectoryLock(dir, publish).ran) {
      publish()
    }
  } catch (e) {
    try {
      fs.unlinkSync(temporary)
    } catch {
      // Never made.
    }
    logForDebugging(
      `[Sandbox Linux] Could not record the mount points this command relies on (${String(e)}) - they are left on the host`,
      { level: 'warn' },
    )
    return undefined
  }
  ownManifests.set(file, { commandKey, over: false })
  return { dir, file }
}

/**
 * Drop the manifest of a wrap that never produced a command. No sandbox can
 * hold its lock, so the mount points it named are no one's.
 */
export function discardMountPointManifest(file: string): void {
  ownManifests.delete(file)
  try {
    fs.unlinkSync(file)
  } catch {
    // Collected already.
  }
}

/**
 * The path of every file in `dirs`. A directory that cannot be listed adds
 * nothing.
 */
function filesIn(dirs: readonly string[]): string[] {
  return dirs.flatMap(dir => {
    try {
      return fs.readdirSync(dir).map(name => path.join(dir, name))
    } catch {
      return []
    }
  })
}

/**
 * The mount points the manifests name, on one reading of every directory this
 * process believes (see {@link believedManifestDirectories}): `live` by a
 * manifest whose sandbox may still be running, `named` by any manifest. What
 * only a finished manifest names is a leftover the next pass removes.
 *
 * `live` is empty when /proc/locks cannot be read, and a directory that cannot
 * be listed adds to neither: a wrap takes a path for a mount point on a
 * manifest's word only, so with none to read it takes every existing path for
 * the caller's own.
 */
export function namedMountPoints(): { live: Set<string>; named: Set<string> } {
  const live = new Set<string>()
  const named = new Set<string>()
  if (!onLinux()) {
    return { live, named }
  }
  ensureManifestDirectory()
  const dirs = believedManifestDirectories()
  const locks = dirs.length > 0 ? readLocks(dirs) : undefined
  for (const file of filesIn(dirs)) {
    if (!file.endsWith(MANIFEST_SUFFIX)) continue
    const manifest = readManifest(file)
    if (manifest === undefined) continue
    const isLiveOne = locks !== undefined && isLive(manifest, locks)
    for (const mountPoint of manifest.paths) {
      named.add(mountPoint)
      if (isLiveOne) {
        live.add(mountPoint)
      }
    }
  }
  return { live, named }
}

/**
 * Whether `p` is still something a clean-up would remove on a manifest's word:
 * the empty file bubblewrap made, or an empty directory of the user's.
 */
function isEmptyMountPoint(p: string): boolean {
  if (isBwrapFileMountPoint(p)) {
    return true
  }
  try {
    const stat = fs.lstatSync(p)
    return (
      stat.isDirectory() &&
      stat.uid === process.getuid?.() &&
      fs.readdirSync(p).length === 0
    )
  } catch {
    return false
  }
}

/**
 * The mount points a sandbox that may still be running relies on, as the
 * manifests say at the moment of the call. For a caller that removes paths of
 * its own accord after a command: removing a mount point from under a running
 * sandbox lifts the deny there.
 *
 * A snapshot, taken without a lock, that may be out of date by the time the
 * caller acts. Its only safe use is to SKIP a removal; a path not being in it
 * never means the path is free to write.
 *
 * A path is in the set only when both hold:
 *
 * - a manifest names it, and that manifest is live by the clean-up's rule or
 *   its liveness cannot be told (/proc/locks unreadable, or an unreadable
 *   manifest that is locked or new), in which case every named path counts;
 * - what is at the path now is still an empty placeholder: an empty regular
 *   file with no write bit and one link, or an empty directory, and the user's.
 *   So a stale or forged manifest never makes a caller spare a file with
 *   content.
 *
 * Paths are as the wraps recorded them: absolute, links above the last
 * component resolved. It answers for every manifest directory this process
 * believes (see {@link believedManifestDirectories}), so a sandbox whose
 * process keeps manifests elsewhere is not seen. Makes nothing on the host.
 * Empty off Linux and where no manifest directory exists.
 */
export function liveMountPoints(): ReadonlySet<string> {
  const spared = new Set<string>()
  const dirs = onLinux() ? believedManifestDirectories() : []
  if (dirs.length === 0) {
    return spared
  }
  const locks = readLocks(dirs)
  const live = new Set<string>()
  const named = new Set<string>()
  let cannotTell = locks === undefined
  for (const file of filesIn(dirs)) {
    if (!file.endsWith(MANIFEST_SUFFIX)) continue
    const manifest = readManifest(file)
    if (manifest === undefined) {
      // Gone since the listing, or not to be read: held to what the clean-up
      // holds it to.
      try {
        const stat = fs.statSync(file, { bigint: true })
        cannotTell ||=
          locks === undefined ||
          holdsLock(locks, {
            file,
            inode: String(stat.ino),
            device: deviceOf(stat.dev),
          }) ||
          Date.now() - Number(stat.mtimeMs) < MANIFEST_GRACE_MS
      } catch {
        // Gone.
      }
      continue
    }
    const isLiveOne = locks !== undefined && isLive(manifest, locks)
    for (const mountPoint of manifest.paths) {
      named.add(mountPoint)
      if (isLiveOne) {
        live.add(mountPoint)
      }
    }
  }
  for (const mountPoint of cannotTell ? named : live) {
    if (isEmptyMountPoint(mountPoint)) {
      spared.add(mountPoint)
    }
  }
  return spared
}

/**
 * Release the manifests of the wraps of this process that `release` says are
 * over, and remove every mount point no live manifest names, from any process,
 * at any time, any number of times. Returns the mount points removed. Does
 * nothing anywhere but on Linux.
 *
 * One pass for each directory this process believes, under that directory's
 * lock: a pass removes what the finished manifests of its own directory name,
 * and goes by the manifests of every directory for what is still relied on.
 */
export function collectMountPoints(
  release: OwnManifestRelease = 'all',
): string[] {
  if (!onLinux()) {
    return []
  }
  // Recorded first and kept whatever becomes of this pass, so a later pass
  // knows these commands are over even when told to release nothing.
  for (const own of ownManifests.values()) {
    if (
      release === 'all' ||
      (release !== 'none' && own.commandKey === release.commandKey)
    ) {
      own.over = true
    }
  }
  ensureManifestDirectory()
  const dirs = believedManifestDirectories()
  const removed: string[] = []
  for (const dir of dirs) {
    const collected = withDirectoryLock(dir, () => collectUnderLock(dir, dirs))
    if (collected.ran) {
      removed.push(...collected.value)
      continue
    }
    logForDebugging(
      collected.held
        ? `[Sandbox Linux] The lock on the mount point directory could not be had, leaving this pass to whoever has it: ${dir}`
        : `[Sandbox Linux] No lock can be taken on the mount point directory from here, so nothing is collected from it until that is put right: ${dir}`,
    )
  }
  return removed
}

/**
 * One pass over `dir`, made under that directory's lock where the caller could
 * take it. `dirs` is every directory this process believes, `dir` among them: a
 * mount point stays while a live manifest in any of them names it, and what is
 * removed is what the finished manifests of `dir` name.
 *
 * A manifest is all that names its mount points, so it is removed last, and
 * only when every path it names is gone or is no longer a mount point: a pass
 * that turns back, or a removal that is refused, leaves it for a later pass.
 * Manifests the caller has said are over are judged as if their writer were
 * gone.
 *
 * The lock does not exclude (see {@link withDirectoryLock}), so before the
 * first removal, and again at {@link LISTING_GOOD_FOR_MS}, the pass lists every
 * directory again: a manifest that was not there at first keeps everything it
 * names, which is how a sandbox about to start on the same path shows. And
 * every {@link REMOVALS_PER_LOOK} removals or {@link LOCKS_GOOD_FOR_MS} it
 * reads /proc/locks again: a manifest locked since keeps what it names. What
 * remains is a pass held up between a look and the removal for longer than a
 * sandbox takes to reach its binds; it then removes that sandbox's mount point.
 */
function collectUnderLock(dir: string, dirs: readonly string[]): string[] {
  // Every file in every directory, or nothing: a directory that is believed
  // and cannot be listed may hold the manifest of a running sandbox.
  const listEveryDirectory = (): string[] =>
    dirs.flatMap(each =>
      fs.readdirSync(each).map(name => path.join(each, name)),
    )
  const isHere = (file: string): boolean => path.dirname(file) === dir
  let files: string[]
  try {
    files = listEveryDirectory()
  } catch (e) {
    logForDebugging(
      `[Sandbox Linux] The mount point manifests could not be listed (${String(e)}) - nothing removed`,
      { level: 'warn' },
    )
    return []
  }
  const manifests: Manifest[] = []
  const unreadable: string[] = []
  for (const file of files) {
    if (!file.endsWith(MANIFEST_SUFFIX)) continue
    const manifest = readManifest(file)
    if (manifest === undefined) {
      unreadable.push(file)
    } else {
      manifests.push(manifest)
    }
  }
  const locks = readLocks(dirs)
  if (locks === undefined) {
    return []
  }
  // The first listing: whatever is found later is a newcomer.
  const known = new Set(files)
  // Forget own manifests that something else has removed.
  for (const file of ownManifests.keys()) {
    if (isHere(file) && !known.has(file)) {
      ownManifests.delete(file)
    }
  }

  // An unreadable manifest names mount points that cannot be honoured one by
  // one. While it is locked, or new enough that a sandbox may be starting,
  // nothing at all is removed.
  let unreadableIsLive = false
  for (const file of unreadable) {
    let stat: fs.BigIntStats
    try {
      stat = fs.statSync(file, { bigint: true })
    } catch {
      continue
    }
    const age = Date.now() - Number(stat.mtimeMs)
    if (
      holdsLock(locks, {
        file,
        inode: String(stat.ino),
        device: deviceOf(stat.dev),
      }) ||
      age < MANIFEST_GRACE_MS
    ) {
      unreadableIsLive = true
    } else if (isHere(file) && age > UNREADABLE_MANIFEST_MAX_AGE_MS) {
      try {
        fs.unlinkSync(file)
      } catch {
        // Gone already.
      }
    }
  }
  if (unreadableIsLive) {
    logForDebugging(
      '[Sandbox Linux] A mount point manifest a sandbox is running under could not be read - leaving every mount point where it is',
      { level: 'warn' },
    )
    return []
  }

  // What a process killed between writing a file and moving it into place
  // left. Nothing reads these, and nothing else removes them.
  for (const file of files) {
    if (!isHere(file) || !file.endsWith(TEMPORARY_SUFFIX)) continue
    try {
      if (
        Date.now() - fs.lstatSync(file).mtimeMs >
        UNREADABLE_MANIFEST_MAX_AGE_MS
      ) {
        fs.unlinkSync(file)
      }
    } catch {
      // Moved into place, or removed by its writer, in the meantime.
    }
  }

  // Over, by the caller's word, unless a sandbox still holds the lock.
  for (const manifest of manifests) {
    manifest.released =
      ownManifests.get(manifest.file)?.over === true &&
      !holdsLock(locks, manifest)
  }

  const finished: Manifest[] = []
  const claimed = new Set<string>()
  const claim = (manifest: Manifest): void => {
    for (const named of [...manifest.paths, ...manifest.sources]) {
      claimed.add(named)
    }
  }
  for (const manifest of manifests) {
    if (isLive(manifest, locks)) {
      claim(manifest)
    } else {
      finished.push(manifest)
    }
  }
  // Each path once, and as a mount point where a manifest names it as one. Only
  // what the finished manifests of this directory name.
  const candidates = new Map<string, boolean>()
  for (const manifest of finished) {
    if (!isHere(manifest.file)) continue
    for (const mountPoint of manifest.paths) {
      if (!claimed.has(mountPoint)) {
        candidates.set(mountPoint, false)
      }
    }
    for (const source of manifest.sources) {
      if (!claimed.has(source) && !candidates.has(source)) {
        candidates.set(source, true)
      }
    }
  }

  // `revived`: manifests that read as finished at first and as locked on a
  // later look. Only the lock can change; a gone writer does not come back.
  const revived = new Set<Manifest>()
  let removalsOnThisLook = 0
  let lookedAt: number | undefined
  let listedAt: number | undefined
  const locksAreFresh = (): boolean =>
    lookedAt !== undefined &&
    removalsOnThisLook < REMOVALS_PER_LOOK &&
    performance.now() - lookedAt < LOCKS_GOOD_FOR_MS
  const listingIsFresh = (): boolean =>
    listedAt !== undefined && performance.now() - listedAt < LISTING_GOOD_FOR_MS
  const readTheLocksAgain = (): boolean => {
    const locksNow = readLocks(dirs)
    if (locksNow === undefined) {
      return false
    }
    for (const manifest of finished) {
      if (!revived.has(manifest) && holdsLock(locksNow, manifest)) {
        revived.add(manifest)
        claim(manifest)
      }
    }
    removalsOnThisLook = 0
    lookedAt = performance.now()
    return true
  }
  const listTheDirectoryAgain = (): boolean => {
    let filesNow: string[]
    try {
      filesNow = listEveryDirectory()
    } catch {
      return false
    }
    for (const file of filesNow) {
      if (!file.endsWith(MANIFEST_SUFFIX) || known.has(file)) continue
      known.add(file)
      const arrived = readManifest(file)
      if (arrived !== undefined) {
        // Published since the pass began: a sandbox is about to start under
        // it, or has. Whatever it names stays, with no further question.
        claim(arrived)
      } else if (fs.existsSync(file)) {
        // There, and not to be read: what it names cannot be kept path by
        // path, so everything is.
        logForDebugging(
          `[Sandbox Linux] A mount point manifest that appeared during the pass could not be read - leaving the rest where it is: ${file}`,
          { level: 'warn' },
        )
        return false
      }
    }
    listedAt = performance.now()
    return true
  }
  // Locks first, listing last: reading /proc/locks can take milliseconds, and a
  // listing made before it would be out of date.
  const mayStillRemove = (): boolean =>
    (locksAreFresh() || readTheLocksAgain()) &&
    (listingIsFresh() || listTheDirectoryAgain())

  const removed: string[] = []
  const notRemoved = new Set<string>()
  for (const [candidate, isSource] of candidates) {
    if (!mayStillRemove()) {
      return removed
    }
    if (claimed.has(candidate)) {
      continue
    }
    const outcome = isSource
      ? removeMountSource(candidate)
      : removeMountPoint(candidate)
    removalsOnThisLook++
    if (outcome === 'removed') {
      removed.push(candidate)
    } else if (outcome === 'failed') {
      notRemoved.add(candidate)
    }
  }
  // The manifests themselves, last. Only a lock taken since can speak for one
  // of these; a manifest somebody else has published in the meantime cannot.
  for (const manifest of finished) {
    if (!isHere(manifest.file)) continue
    if (!locksAreFresh() && !readTheLocksAgain()) {
      return removed
    }
    if (revived.has(manifest)) {
      continue
    }
    // A mount point that could not be removed from here is still somebody's to
    // remove, and the manifest is all that says so.
    if (
      [...manifest.paths, ...manifest.sources].some(named =>
        notRemoved.has(named),
      )
    ) {
      continue
    }
    try {
      fs.unlinkSync(manifest.file)
    } catch {
      // Collected by another process already.
    }
    ownManifests.delete(manifest.file)
    removalsOnThisLook++
  }
  return removed
}

/**
 * Put directories of a test's own in the place of those the manifest
 * directories are looked for in (see {@link ManifestDirectoryPlaces}), or, with
 * nothing, put the real ones back. Test seam, and nothing else may call it: the
 * real places are shared with every other process of the user. A place that is
 * left out stays what it really is. Which directory the manifests are written
 * to is forgotten with it, so the next use works it out again.
 */
export function setMountPointManifestPlacesForTesting(
  places?: Partial<ManifestDirectoryPlaces>,
): void {
  placesForTesting = places
  manifestDirectory = undefined
  manifestDirectoryIsPrivate = false
  manifestDirectoryUnavailable = false
  directoryFailureLogged = false
}
