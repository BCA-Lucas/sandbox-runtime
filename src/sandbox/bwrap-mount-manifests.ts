/**
 * Which mount points on the host a running sandbox still relies on (Linux).
 *
 * A deny on a path that does not exist needs a mount point there: bwrap makes
 * an empty file (or, for an intermediate component, an empty directory) on the
 * host and binds /dev/null or an empty directory over it. Unlinking that file
 * while a sandbox is still bound over it detaches the mount inside that
 * sandbox — the denied path can then be created, and what is written lands on
 * the host. A mount point may therefore only be removed when no running
 * sandbox relies on it, and nothing a process counts for itself can decide
 * that: a second srt process, a caller that crashes, one that cleans up early,
 * twice or never, each gets a different answer.
 *
 * The kernel is asked instead. Each wrap writes a manifest naming the mount
 * points it relies on into a per-user runtime directory and passes
 * `--lock-file <manifest>` to bwrap. bubblewrap's sandbox init process opens
 * that path and holds an fcntl read lock (F_RDLCK through F_SETLK) on it for
 * exactly the sandbox's lifetime; the kernel drops the lock however the
 * sandbox ends, SIGKILL included. /proc/locks then answers, for any process
 * and at any moment, whether a sandbox that named a mount point is still
 * running, so cleanup becomes a garbage collect any process may run at any
 * time and any number of times: a mount point goes only when no live manifest
 * names it.
 *
 * The lock belongs to the sandbox's init process, not to the command: bwrap
 * opens the manifest with O_CLOEXEC, so the descriptor does not survive the
 * exec into the command, and a POSIX lock is only dropped by the process that
 * took it.
 *
 * Two processes of one user keep each other's mount points only when each
 * reads what the other writes, so where the manifests go is worked out from
 * the user id and the file system before the environment, which differs
 * between a login shell and what a service, an IDE or cron starts: see
 * {@link manifestDirectoryCandidates}. A process writes to the first of those
 * directories it can use, and believes what it finds in the ones that come
 * from the user id, or, where it can use none of those, in the ones its
 * environment names (see {@link believedManifestDirectories}).
 *
 * Every one of them is bound read-only into every sandbox that restricts
 * writes at all, whether or not its own invocation names a manifest, and
 * whichever of them the wrapping process writes to (see
 * {@link mountPointManifestDirectories}), so a sandboxed command can neither
 * delete nor rewrite a manifest, its own or another sandbox's; one that is
 * not there is made first, so that the command cannot make it itself, with
 * manifests of its own in it; and the directories between each of them and
 * the write root it lies in are pinned there, so that the command cannot
 * rename one aside and make the directory again under the old name.
 * What that leaves out is a sandbox this library did not start, or an older
 * release of it did, with a directory writable, the sandbox of a process with
 * another environment where a process has to keep its manifests under a name
 * its own environment gives, and a directory whose name, or a name above it,
 * is a link inside a write root, or whose parent is not there yet below one:
 * neither can be pinned.
 *
 * Both of the kernel's answers are relative to a PID namespace: /proc/locks
 * lists a lock only when its holder has a pid in the namespace of the /proc
 * being read, and /proc/PID is local to it. A manifest therefore says which
 * PID namespace wrote it, and a process in another one does not judge it at
 * all: to that process it is live, and only a process in the namespace that
 * wrote it, which can see both answers, ever collects what it names.
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
 * A manifest written this recently counts as live even with no lock on it and
 * its writer gone. bubblewrap takes the lock in the sandbox's init process,
 * which it forks alongside the command, so a wrapping process killed between
 * the exec and that fcntl would otherwise leave a starting sandbox's mount
 * point unclaimed. The window to cover is bubblewrap's own startup, a few
 * milliseconds; this is two orders of magnitude more, and short enough that a
 * mount point a killed process left behind is collectable while the command
 * after it is still being wrapped.
 */
const MANIFEST_GRACE_MS = 500

/** How long a collect or a publish waits for the directory lock. */
const DIRECTORY_LOCK_WAIT_MS = 2_000

/** Between attempts at the directory lock. */
const DIRECTORY_LOCK_RETRY_MS = 25

/**
 * A directory lock this old is broken whoever holds it, a holder that is
 * still running included: far past the milliseconds a collect takes. It is
 * the only way out for a holder that cannot be asked after, one in another
 * PID namespace or one whose lock says nothing this process can read. A
 * holder in this namespace is asked after directly, and the lock of one that
 * is gone is broken at once, whatever its age.
 */
const DIRECTORY_LOCK_STALE_MS = 60_000

/**
 * How many mount points a pass removes on one look at /proc/locks, and for how
 * long one look is good. Each look reads all of /proc/locks, whose size is the
 * host's and not this library's, so one per removal made a pass over many
 * mount points on a busy host outlast the wait above. A removal takes some ten
 * microseconds, and a sandbox takes several milliseconds, about four on a fast
 * machine, to get from its manifest being published to its binds being in
 * place (the wrap returns, the caller spawns a shell, bubblewrap sets up its
 * namespaces), so a look shared by this many removals, under a millisecond's
 * worth, is as good as one each. The time limit is for a pass that is held up
 * between two removals, which then looks again before the next, and is kept
 * under that start-up time.
 */
const REMOVALS_PER_LOOK = 64
const LOCKS_GOOD_FOR_MS = 2

/**
 * For how long one listing of the manifest directory is good. A manifest
 * published for a sandbox that is about to start is the usual way for a pass
 * to be out of date, and listing a directory of a few manifests costs less
 * than one removal, so this is kept an order of magnitude under the time that
 * sandbox needs to get to its binds, and not at the two milliseconds above. It
 * is a time and not "before every removal" so that a directory of thousands of
 * manifests, which takes milliseconds to list, is not listed thousands of
 * times.
 */
const LISTING_GOOD_FOR_MS = 0.25

/**
 * A manifest whose contents cannot be read is dropped once it is this old and
 * no sandbox holds its lock — long past anything that could still be using
 * what it names, and long enough that another version of this library writing
 * to the same directory keeps its manifests for as long as it needs them.
 */
const UNREADABLE_MANIFEST_MAX_AGE_MS = 60 * 60 * 1000

/**
 * The largest file that is read as a manifest. One names a wrap's mount
 * points, some dozens of paths, and is a few kilobytes; whatever is larger
 * than this is not one, and is not read into memory to find that out.
 */
const MANIFEST_MAX_BYTES = 1024 * 1024

/**
 * What a manifest, and the directory lock, is written as before it is moved
 * into place. A process killed between the two leaves the file behind, and a
 * pass removes one that is as old as an unreadable manifest has to be.
 */
const TEMPORARY_SUFFIX = '.tmp'

const ManifestSchema = z.object({
  version: z.literal(MANIFEST_VERSION),
  /** The process that wrapped, and its start time, to tell a recycled pid. */
  pid: z.number().int().nonnegative(),
  start: z.string(),
  /**
   * The PID namespace the wrapping process was in, as `readlink
   * /proc/self/ns/pid` names it. `pid` and the lock bubblewrap takes can only
   * be asked after from there. Absent from a manifest written before the field
   * existed, which is then from a namespace nobody can name.
   */
  ns: z.string().optional(),
  /** When the manifest was written, for {@link MANIFEST_GRACE_MS}. */
  created: z.number(),
  /** The mount points bwrap makes on the host for that wrap's deny paths. */
  paths: z.array(z.string()),
  /**
   * The empty directories those mount points bind FROM, which this library
   * makes itself. A live bind's source must stay, so they go the same way the
   * mount points do, and are held to what {@link removeMountSource} asks: a
   * source that is no longer our own private empty directory is not ours to
   * remove.
   */
  sources: z.array(z.string()),
})

type Manifest = z.infer<typeof ManifestSchema> & {
  file: string
  /** The inode /proc/locks reports a lock on, and the device it is on. */
  inode: string
  device: string
  /**
   * Whether this process has given the manifest up: it wrote it, the caller
   * says the command is done, and nothing held the lock when the pass began.
   * Its writer is running and it may be young, and neither keeps it: only a
   * lock can still make it live. The file stays where it is until the end of
   * the pass, like any other finished manifest's.
   */
  released: boolean
}

/**
 * Manifests this process wrote and that are still on disk as far as it knows,
 * each with the key of the command it was wrapped for where the caller gave
 * the wrap one, and whether the caller has said that command is over. That is
 * remembered, not acted on at once: a pass can turn back half way, a removal
 * can be refused, a sandbox can still hold the lock, and in each case the
 * manifest has to stay on disk, since it is all that names the mount points,
 * and go at a later pass whatever that pass is told to release.
 */
const ownManifests = new Map<
  string,
  { commandKey: string | undefined; over: boolean }
>()

/**
 * Which of this process's own manifests a collect may release. Releasing one
 * says "the command this was wrapped for is over", which only the caller
 * knows, so it is the caller that says which:
 * - `all`: no wrap of this process is outstanding, or the process is ending;
 * - `none`: some are, and nothing says which of them is over, so only what
 *   OTHER processes have finished with is taken away;
 * - one command: that command is over, whatever else is still running.
 * Releasing the manifest of a wrap whose command has not started yet is what
 * must never happen: bubblewrap opens the manifest to lock it, and a command
 * whose manifest is gone refuses to start, or, if it got its lock in the
 * moment between the pass's last look at /proc/locks and the unlink, runs on
 * with nothing on disk naming its mount points.
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
 * Field 22 of /proc/PID/stat, the process's start time in clock ticks. The
 * comm field can hold spaces and parentheses, so the fields are counted from
 * the last ')' rather than from the start of the line.
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
 * Whether the process a manifest names is still running. Only "the process is
 * gone" answers no: a /proc that cannot be read must not make a live sandbox's
 * manifest collectable.
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

/**
 * The PID namespace this process is in, as the kernel names it
 * (`pid:[4026531836]`), or `undefined` where it cannot be told.
 */
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

/**
 * The device half of what /proc/locks prints for a file, from the number stat
 * gives for it: `major:minor`, in decimal.
 */
function deviceOf(dev: bigint): string {
  const major = ((dev >> 8n) & 0xfffn) | ((dev >> 32n) & ~0xfffn)
  const minor = (dev & 0xffn) | ((dev >> 12n) & ~0xffn)
  return `${major}:${minor}`
}

/**
 * The filesystems on which the device stat reports for a file is the one
 * /proc/locks prints for a lock on it: both are the superblock's. It is not so
 * everywhere - a btrfs subvolume and some overlay arrangements give stat a
 * device of their own - and there only the inode number can be compared.
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
 * Whether /proc/locks lists a lock on this file. Any lock on a manifest is the
 * one bubblewrap's sandbox init holds: nothing else opens one to lock it.
 *
 * The device is compared where the manifests' filesystem reports the one
 * /proc/locks prints, and only there. Inode numbers are per filesystem, and on
 * a tmpfs they are small and handed out in order, so a manifest in a young
 * runtime directory can share its number with some unrelated locked file on
 * another filesystem; it then read as live for as long as that lock was held,
 * and every path it named as a mount point for every later wrap.
 * Where the two devices cannot be compared the inode number alone decides,
 * which errs towards "locked": the other way round would hide a live
 * sandbox's lock.
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
 * What /proc/locks lists, for the manifests in `dirs`. Only the locks whose
 * holder has a pid in the PID namespace of the /proc being read are listed,
 * which is why a manifest from another namespace is never judged by this.
 *
 * `undefined` when the list could not be read, which every caller reads as
 * "every manifest is locked".
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
 * Make `dir` a directory of ours alone, or say it cannot be.
 *
 * The name is predictable and sits where sandboxed commands commonly write,
 * so what is found there is looked at before it is touched: through a
 * descriptor opened without following a link, so that a symlink planted at
 * the name is refused rather than having its target's mode changed, and the
 * mode is set on that descriptor, never on the path.
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
 * Whether a manifest kept under `dir` would be out of bubblewrap's reach: the
 * wrap mounts a fresh /dev and /proc after every bind, which buries whatever
 * was bound beneath them, and bubblewrap opens the manifest after its mounts.
 */
function isBuriedBySandboxMounts(dir: string): boolean {
  return ['/dev', '/proc', '/sys'].some(
    root => dir === root || dir.startsWith(`${root}/`),
  )
}

/**
 * The places the manifest directories are looked for in. The first two are
 * the same for every process of a user, whatever started it; the last two are
 * what this process's environment says.
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
 * Whether `dir` is a runtime directory of this user's as the system makes
 * one: a real directory, not a link to one, the user's, and nobody else's to
 * look into.
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
 * Where the directory `name` names really is, as far as that can be told
 * before it is made: under its parent as the links above it resolve, by its
 * own last component.
 */
function whereItReallyIs(name: string): string {
  try {
    return path.join(fs.realpathSync(path.dirname(name)), path.basename(name))
  } catch {
    return path.resolve(name)
  }
}

/**
 * The names under which the processes of this user keep their manifests where
 * several can find them, in the order they are tried for writing:
 * - `/run/user/UID/srt-mount-points`, where `/run/user/UID` is a runtime
 *   directory of the user's (see {@link isTheUsersRuntimeDirectory});
 * - `/tmp/srt-mount-points-UID`;
 * - `$XDG_RUNTIME_DIR/srt-mount-points`, where that is set;
 * - `srt-mount-points-UID` under the system temp dir, which is `$TMPDIR`'s.
 *
 * The user id and the file system come first because they are the same for
 * every process of the user. The environment is not: a login shell and what a
 * service, an IDE, cron or `docker exec` starts differ in `XDG_RUNTIME_DIR`,
 * two shells can differ in `TMPDIR`, and two processes that each wrote where
 * their own environment said never read each other's manifests. The second
 * wrap then took the first's mount point for the user's own file, and the
 * first's clean-up removed it from under the second sandbox. The names from
 * the environment stay, last, for a process that can use neither of the first
 * two.
 *
 * Two names for one directory are one, the earlier, by where they really are.
 * One that a sandbox's own mounts would bury is left out.
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
 * The directory this process writes its manifests to: the first of the shared
 * names (see {@link sharedManifestDirectoryNames}) that is, or can be made, a
 * directory of ours alone that we can write, else - when none can, as in a
 * sandbox that binds them read-only - a private directory only this process
 * knows, which keeps the guarantee within this process and loses only what
 * other processes would have read.
 *
 * Revalidated on every use: the temp dir is somewhere sandboxed commands
 * commonly write, and a directory swapped for a symlink between two wraps
 * would put manifests somewhere else entirely.
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
 * Every directory whose manifests this process believes, for a wrap, a
 * clean-up and {@link liveMountPoints} to read:
 * - each of the names that come from the user id that is there and is a
 *   directory of ours alone that we can write, whichever of them this process
 *   writes to;
 * - the names the environment gives, held to the same, only where none of
 *   the first kind will do, which is where this process writes to one of
 *   them;
 * - the one this process has settled on, whatever it is.
 *
 * What the environment names is kept out of a sandboxed command's reach by
 * the processes whose environment names it, and by no other: a process with
 * another temp dir does not know of it, and its command may write there. A
 * manifest planted that way would keep a path, or have one removed, on the
 * word of a process that never relied on the directory, so it is believed
 * only by a process that has nowhere else to keep its own. Nothing is lost by
 * that: every process that can use a name from the user id meets every other
 * one there.
 *
 * One that is a link, somebody else's, open to others or not to be written is
 * passed over: what is in it is not believed, and nothing fails for it.
 * Nothing is made.
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
 * Every directory a sandbox must not be able to write, because some process
 * of this user keeps manifests in it and a collect on the host believes what
 * it finds there: every shared name, as this process sees them, and the one
 * this process has settled on where that is none of them. For a wrap to bind
 * read-only, whether or not it has a manifest of its own.
 *
 * Every name, and not only the one this process writes to: every process of
 * the user believes what is under the ones that come from the user id, and
 * one with this environment that can use none of those what is under the
 * ones the environment gives, so a sandbox with the temp dir writable could
 * otherwise delete and forge manifests in the one under it while its own
 * process writes under the runtime directory. Each is made if it can be, so
 * that a sandboxed command cannot make it first and fill it before a process
 * that will believe it comes along: the command runs as the user, so what it
 * makes passes every check of owner and mode, which keep other users out and
 * not the command. One that is there and the user's is listed even when it
 * cannot be written from here. The last resort is not made for this: there is
 * nothing to keep out of reach in a directory nobody has made. A wrap that is
 * about to record says so with `recording`, and the directory its manifest
 * will go to is then settled first, the last resort included: the wrap has to
 * know every one of these before it publishes, to pin what lies above them.
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
 * Take away the directory only this process knows, once nothing is left in
 * it, when the process or its session is ending: nobody else would. With the
 * manifest of a sandbox that is still running in it, it stays.
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

/**
 * What a process leaves in the directory lock: who it is, and the PID
 * namespace in which that can be asked after.
 */
function directoryLockContent(): string {
  return `${process.pid} ${processStartTime(process.pid) ?? '?'} ${ownPidNamespace() ?? '?'}\n`
}

/**
 * Take the directory lock, and say what it now holds, or why it was not taken:
 * `held` when something is at its name already, `unavailable` when this
 * process cannot make one there at all.
 *
 * The lock comes into being whole. Made with O_EXCL and written to afterwards
 * it stood empty for a moment, and a waiter that read it then found no holder
 * in it and removed it at once, so two processes were inside together. It is
 * written under another name and linked into place instead: link fails when
 * the name is taken, exactly as O_EXCL does, and what it puts there is never
 * seen half made. A filesystem without hard links gets no lock, and no pass.
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
 * Give the directory lock up, if it is still this process's. One broken for
 * its age while this process was held up belongs to whoever took it next, and
 * removing that one by name let a third process in beside it.
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
 * What stands at the directory lock's name, once taking it has failed:
 * - `free`: nothing any more, or the lock of a holder that is gone, removed;
 * - `held`: somebody's lock, to be waited for;
 * - `stuck`: something this process can neither read as a lock nor remove,
 *   which no amount of waiting changes.
 *
 * Breaking a lock is three steps - read who holds it, ask after them, unlink -
 * and not one, so two waiters can both find the same holder gone and the
 * slower one's unlink can land on the lock a third process has taken since.
 * Nothing here prevents that. It is why nothing rests on this lock: see
 * {@link withDirectoryLock}.
 */
function examineDirectoryLock(lockFile: string): 'free' | 'held' | 'stuck' {
  let holder: string
  let age: number
  try {
    // Looked at before it is opened, and opened without blocking or following
    // a link: opening a FIFO to read waits for a writer, and nothing but a
    // regular file is a lock this library made.
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
    // Gone between the failed attempt and this look: the next attempt takes
    // it. Anything else is a file that is there and cannot be read.
    return (e as NodeJS.ErrnoException).code === 'ENOENT' ? 'free' : 'stuck'
  }
  // A holder can be asked after only in the PID namespace it named, when that
  // is this one: elsewhere its pid means nothing, or means some other
  // process. One that cannot be asked after is believed until the lock is
  // older than any pass, as is one that did not say who it is.
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
    // Another process broke it first; or it cannot be removed from here, in
    // which case it is still there and the next attempt would find it so.
    return (e as NodeJS.ErrnoException).code === 'ENOENT' ? 'free' : 'stuck'
  }
  return 'free'
}

/**
 * Run `body` while holding the manifest directory's lock, and report whether
 * it ran, and if not, whether that was for somebody `held` it all the while.
 * It gives up, without running `body`, after {@link DIRECTORY_LOCK_WAIT_MS} of
 * finding the lock held, and at once when what is at the lock's name is
 * nothing it could ever take: the wait is this thread's, in the wrap, in the
 * clean-up after every command and in the exit handler, and nothing about a
 * lock is worth more of it than that.
 *
 * The lock keeps srt processes out of each other's way most of the time; it
 * does not exclude, and nothing may rest on it. Its holder can be held up past
 * the age at which it is broken, the break itself is not atomic (see
 * {@link examineDirectoryLock}), and a publish that cannot have the lock goes
 * ahead without it. What makes a mount point safe to remove is looked at
 * again immediately before the removals and at short intervals during them:
 * the directory, for a manifest that was not there when the pass began, and
 * the kernel's answer about every manifest the pass knows of (see
 * {@link collectUnderLock}).
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
    // On every round, whatever the look above found: a lock that is broken
    // and taken again by others for as long as this process keeps asking is
    // as good as held.
    if (Date.now() >= deadline) {
      return { ran: false, held: true }
    }
    sleep(DIRECTORY_LOCK_RETRY_MS)
  }
}

/**
 * What is at a manifest's name, read as one, or `undefined` when it is not a
 * manifest this version can read. Only a regular file of the user's, no
 * larger than {@link MANIFEST_MAX_BYTES}, is read at all, and it is looked at
 * through the descriptor it is then read from, opened without following a
 * link and without blocking: opening a FIFO to read waits for a writer, a
 * link leads wherever whoever planted it likes, and nothing but such a file
 * is a manifest this library wrote.
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
 * THIS process can tell.
 *
 * It can tell only about a manifest written in its own PID namespace: the
 * writer's pid and the sandbox's lock are both invisible from any other. So a
 * manifest from another namespace is live here whatever /proc says, for good:
 * what it names is collected by a process in the namespace that wrote it, and
 * by nobody if that namespace has gone, which leaves empty files behind and
 * opens nothing. One that does not say where it is from is live while a
 * process with its writer's pid and start time can be seen, and otherwise
 * until it is as old as an unreadable manifest has to be to be dropped.
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
 * What became of a path a pass set out to remove: `left` when there is
 * nothing more to do about it - it is gone, or is no longer what bubblewrap or
 * this library made - and `failed` when it is still that and could not be
 * removed from here, which a later pass, or another process, may yet manage.
 */
type Removal = 'removed' | 'left' | 'failed'

/** Whether a failed removal means the path is no longer ours to remove. */
function meansNothingToRemove(e: unknown): boolean {
  const code = (e as NodeJS.ErrnoException | undefined)?.code
  // Not empty after all: something was written into it between the look and
  // the rmdir.
  return isAbsenceErrno(e) || code === 'ENOTEMPTY' || code === 'EEXIST'
}

/**
 * Remove an empty directory a placeholder bound from, if it is still our own.
 * It sits under the system temp dir, which sandboxed commands commonly can
 * write, so anything that is not a private empty directory of ours — a
 * symlink, a directory whose mode has been widened, one with something in it —
 * is somebody else's and is left exactly as found.
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
 * regular file (not a link to one), empty, with no write bit, under one name,
 * and ours. A manifest is only a claim about a path, and the directory it
 * sits in is only as private as its host, so nothing is removed on a
 * manifest's word that does not also look like what bubblewrap leaves.
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
 * What kind of mount point the path a live manifest names still is, by what
 * is there now: an empty regular file, a directory, or neither any more. A
 * manifest says a path was a mount point when it was written; a file that has
 * been written to since, or a link put in its place, is somebody's own.
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
 * Remove a mount point, if it is still the empty file or directory bwrap made.
 * Anything else - a file with content or a write bit, a link, a directory
 * something has written into or that is not ours - is left where it is.
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
 * bind from, before the sandbox that relies on them can start, and say where
 * to point bubblewrap's --lock-file.
 *
 * `undefined` when there is nothing to record, or when no manifest could be
 * written, in which case the caller must not track those mount points at all:
 * what this process cannot record it does not remove. That is as far as it
 * goes. Nothing on disk then says a sandbox relies on them, so a wrap in
 * another process that denies the same path takes the file for the caller's
 * own: it binds it onto itself and names it nowhere, and nobody removes it.
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
  // Written beside the manifest and renamed onto it, so a collect in another
  // process reads it whole or not at all. The rename is made under the
  // directory lock where that can be had, which keeps it out of the middle of
  // most passes, and without it where it cannot: a wrap is not refused for
  // want of a lock. Either way a pass may already have listed the directory,
  // so what keeps this wrap's mount points is that every pass lists it again
  // before it removes anything (see collectUnderLock), and that the sandbox
  // this manifest covers has not started yet.
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
 * The path of every file in `dirs`, for a reading on which nothing is
 * removed: a directory that cannot be listed adds nothing.
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
 * process believes (see {@link believedManifestDirectories}): `live`, by a
 * manifest whose sandbox may still be running, and `named`, by any manifest at
 * all. What only a finished manifest names is what a sandbox that has ended
 * left behind and no pass has collected yet, and the next pass in any process
 * removes it on that manifest's word.
 *
 * `live` is empty when /proc/locks cannot be read, and a directory that
 * cannot be listed adds to neither. A wrap takes an existing path for a mount
 * point on a manifest's word only, never by the look of it, so with none to
 * be read it takes every existing path for the caller's own.
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
 * Whether what is at `p` now is still something a clean-up would take away on
 * a manifest's word: the empty file bubblewrap made (see
 * {@link isBwrapFileMountPoint}), or an empty directory of the user's.
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
 * manifests say at the moment of the call: for a caller that removes paths of
 * its own accord after a command, to leave out the ones in this set. Removing
 * a mount point from under a running sandbox lifts the deny there.
 *
 * It is a snapshot, taken without a lock, from one listing of each manifest
 * directory and one reading of /proc/locks, and it may be out of date by the
 * time the caller acts on it: a sandbox can start on a path the moment after.
 * Its only safe use is to SKIP a removal. That a path is not in it never
 * means the path is free to be written, or that nothing will rely on it.
 *
 * A path is in the set only when both of these hold:
 * - a manifest names it, and that manifest is live by the rule the clean-up
 *   goes by, or its liveness cannot be told. It cannot be told when
 *   /proc/locks cannot be read, or while a manifest that cannot be read is
 *   locked or new; every path that any readable manifest names then counts.
 *   What a manifest that cannot be read names cannot be listed at all;
 * - what is at the path now still has the shape of a mount point: an empty
 *   regular file with no write bit and one link, or an empty directory, and
 *   the user's. So whatever a caller spares on the word of this set is an
 *   empty placeholder, and a manifest that is out of date, or forged, never
 *   makes it spare a file with something in it.
 *
 * The paths are as the wraps recorded them: absolute, with the links in the
 * directories above the last component resolved and the last component as it
 * stands. A caller compares its own paths in that form.
 *
 * The manifests are believed as found. Their directories can be written by
 * the user's own processes outside any sandbox; every sandbox that restricts
 * writes has each of them bound read-only, with the directories between it
 * and the write root it lies in pinned, which does not reach a directory
 * whose name, or a name above it, is a link inside a write root, nor one
 * whose parent is not there yet below one. It answers for every manifest
 * directory this process believes (see {@link believedManifestDirectories}),
 * whichever of them it writes to, so a sandbox of a process that keeps its
 * manifests under a name its environment gives, or in a directory of its own,
 * for want of a name from the user id that it can use, or of something that
 * writes none, is not seen.
 *
 * Makes nothing on the host, a manifest directory included. Empty where
 * there is no manifest directory, and anywhere but on Linux.
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
 * lock: a pass takes off the disk what the finished manifests of its own
 * directory name, and those manifests, and goes by the manifests of every
 * directory for what is still relied on.
 */
export function collectMountPoints(
  release: OwnManifestRelease = 'all',
): string[] {
  if (!onLinux()) {
    return []
  }
  // What the caller says about its own commands is taken down first and kept,
  // whatever becomes of this pass: one that cannot have the lock, or turns
  // back half way, leaves the manifests for the next, which has to know they
  // are done with even when it is told to release nothing.
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
 * One pass over `dir`, which the caller makes under that directory's lock
 * where it can. `dirs` is every directory this process believes, `dir` among
 * them. The pass reads the manifests of all of them, and a mount point stays
 * while a live manifest in any of them names it; what it takes off the disk
 * is what the finished manifests of `dir` name, and those manifests. What the
 * finished manifests of another directory name goes at the pass over that
 * one, under its lock.
 *
 * Nothing is taken off the disk until the end. A manifest is all that names
 * its mount points, so it goes last, after them, and only when every one of
 * them is gone or is no longer a mount point: a pass that turns back half way,
 * or a removal that is refused, leaves the manifest for a later pass to go by.
 * That holds for the manifests of this process as for anybody's. The ones the
 * caller has said are over are judged as if their writer were gone, and that
 * is all that sets them apart.
 *
 * The lock does not exclude (see {@link withDirectoryLock}), so the pass does
 * not rely on the directory staying as first listed. Immediately before it
 * removes anything, and again whenever its last listing is more than
 * {@link LISTING_GOOD_FOR_MS} old, it lists every directory again, where a
 * manifest that was not there at first keeps everything it names whatever
 * else is true of it: that is how a sandbox about to start on the same path
 * shows. And before the first removal, and again every
 * {@link REMOVALS_PER_LOOK} removals or {@link LOCKS_GOOD_FOR_MS}, it reads
 * /proc/locks again, where a manifest that has been locked since keeps what it
 * names. That one covers the actor no lock could: the bubblewrap a wrap has
 * already handed to its caller, which takes its lock whenever the caller
 * starts it. What is left is the time between a look and the removal made on
 * it, a quarter of a millisecond for a newly published manifest and two
 * milliseconds for one that was there all along, against the four or more a
 * sandbox takes to get from its start to its binds. A pass that is held up for
 * longer than that between looking and removing, with a sandbox starting on
 * the same path in that time, still takes that sandbox's mount point away.
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
  // What the pass knows of: the first listing, so that everything found
  // later is a newcomer.
  const known = new Set(files)
  // A manifest of this process that something else has taken off the disk is
  // nothing to remember.
  for (const file of ownManifests.keys()) {
    if (isHere(file) && !known.has(file)) {
      ownManifests.delete(file)
    }
  }

  // A manifest whose contents cannot be read — a file another version of this
  // library wrote, a truncated one, one this process may not read — names
  // mount points that cannot be honoured one by one. While the kernel says a
  // sandbox is running under it, or it is new enough that one may be starting,
  // nothing at all is removed; once it is neither, whatever it names is not in
  // use and it stands in the way of nothing.
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

  // The wraps of this process the caller has said are over, except that one
  // whose manifest is locked has a sandbox running under it all the same, and
  // is anybody's live manifest until the lock goes.
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
  // Each path once, and as a mount point where a manifest names it as one.
  // Only what the finished manifests of this directory name: the others are
  // kept in `finished` to be asked after again, not to be acted on.
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

  // When the pass last made sure, and what it found then: `revived` are the
  // manifests of the first listing that read as finished then and as locked on
  // a later look. A finished manifest's writer is gone and its grace is over,
  // and neither comes back, so the lock is all that is asked after again.
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
  // The kernel's list is read first and the directory listed last. Reading
  // the list takes as long as the host has locks, milliseconds on a busy one,
  // after which a listing made before it is out of date as well.
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
    // A mount point that is still there, still what bubblewrap made, and could
    // not be removed from here - a directory this process sees read-only, say
    // - is still somebody's to remove, and the manifest is all that says so.
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
 * directories are looked for in (see {@link ManifestDirectoryPlaces}), or,
 * with nothing, put the real ones back. Test seam, and nothing else may call
 * it: the real places are every other process's of the user, and a test that
 * lists, attacks or collects there does so to the sandboxes that user is
 * running. A place that is left out stays what it really is, so a test can
 * stand in for `/run/user/UID` and `/tmp` and leave the environment to say the
 * rest.
 *
 * Which directory the manifests are written to is forgotten with it, so that
 * the next use works it out again: this module may have settled on one before
 * the test that wants another was loaded.
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
