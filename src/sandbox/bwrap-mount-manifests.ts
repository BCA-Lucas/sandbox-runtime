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
 * The sandbox vouches for itself. Each wrap writes a manifest naming its mount
 * points, `<id>.json`, into a per-user directory. The command line it hands out
 * is a shell that appends its own /proc/$$/stat line to `<id>.started` and then
 * execs bubblewrap: the process on record is bubblewrap, recorded before it has
 * made a mount, and the wrap always passes --die-with-parent, so the sandbox
 * dies with it. A manifest with a record is live exactly while a process with a
 * recorded pid and start time exists, which any process can ask, so cleanup is
 * a garbage collect any process may run at any time.
 *
 * bubblewrap binds the manifest before it makes a mount point, and a pass
 * claims a finished manifest, renaming it to `<id>.claimed`, before it removes
 * what that names. A command started after the claim fails having made nothing;
 * one that got past it has its record on disk, which the pass reads after the
 * claim. Whatever cannot be read or asked (a manifest, a record, /proc) counts
 * as live: only "no such process" and a different start time end a sandbox.
 *
 * The manifest directories are bound read-only into every sandbox that
 * restricts writes, and the directories above them inside a write root are
 * pinned, so a sandboxed command can neither rewrite a manifest nor swap the
 * directory (see {@link mountPointManifestDirectories}). Not covered: a sandbox
 * this library did not start, a process that looks for its runtime or temp
 * directory elsewhere, and a runtime or temp directory that is a link inside a
 * write root or not there yet.
 *
 * /proc/PID is relative to a PID namespace, so a manifest records the namespace
 * that wrote it and only a process in that namespace judges it; to any other it
 * is live.
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
const STARTED_SUFFIX = '.started'
const CLAIMED_SUFFIX = '.claimed'

/**
 * A manifest this young counts as live with no started record yet, so that a
 * command is not refused its start because the process that wrapped it was
 * killed a moment before.
 */
const MANIFEST_GRACE_MS = 500

/**
 * A pass with no more candidates than this lists the manifest directory again
 * before every removal, so each is judged on a listing a few microseconds old.
 * An ordinary pass is a handful of paths.
 */
const LISTS_BEFORE_EACH_REMOVAL_UP_TO = 64

/**
 * For how long one listing is good in a larger pass: well under the time a
 * starting sandbox needs to reach its binds, and a time so a directory of
 * thousands is not listed thousands of times.
 */
const LISTING_GOOD_FOR_MS = 0.25

/**
 * How often a reading starts over because a listed manifest was gone when it
 * was opened (claimed, given back or collected meanwhile) before it gives up.
 */
const LISTING_ATTEMPTS = 4

/**
 * What is at a manifest's name and is not one this version reads counts as
 * live until it is this old, and is dropped then: long enough for another
 * version of this library to keep its own format.
 */
const UNREADABLE_MANIFEST_MAX_AGE_MS = 60 * 60 * 1000

/** The largest file read as a manifest; a real one is a few kilobytes. */
const MANIFEST_MAX_BYTES = 1024 * 1024

/** The largest started record read: a line of some 300 bytes for each run. */
const RECORD_MAX_BYTES = 64 * 1024

/**
 * Suffix of a manifest before it is moved into place. One left by a killed
 * process is removed at {@link UNREADABLE_MANIFEST_MAX_AGE_MS}.
 */
const TEMPORARY_SUFFIX = '.tmp'

const ManifestSchema = z.object({
  version: z.literal(MANIFEST_VERSION),
  /** The process that wrapped, and its start time, to tell a recycled pid. */
  pid: z.number().int().nonnegative(),
  start: z.string(),
  /**
   * The writer's PID namespace (`readlink /proc/self/ns/pid`): a pid can only
   * be asked after from there. Absent where it could not be read.
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
  /** Where it is: at its own name, `<id>.json`, or at a claim's. */
  file: string
  claimed: boolean
  /** Its started record, `<id>.started`. */
  record: string
  /** This process wrote it and the caller says its command is over. */
  released: boolean
}

/**
 * Manifests this process wrote that are still on disk, by their own name, with
 * the command key the caller gave and whether that command is over. Remembered
 * rather than acted on at once: a manifest must stay on disk until a pass
 * removes what it names.
 */
const ownManifests = new Map<
  string,
  { commandKey: string | undefined; over: boolean }
>()

/**
 * The mount points, and the directories they bind from, of wraps that could
 * record them nowhere. No other process knows of them, so they are this
 * process's to remove once none of its wraps is outstanding: in a pass like
 * any other where there is a directory by then, so that a path another
 * process's manifest names is kept, and on its own word where there is none.
 */
const unrecorded = { paths: new Set<string>(), sources: new Set<string>() }

/**
 * Which of this process's own manifests a collect may release. Only the caller
 * knows that a command is over:
 *
 * - `all`: no wrap of this process is outstanding, or the process is ending;
 * - `none`: some are, and nothing says which is over, so only what other
 *   processes have finished with is collected;
 * - one command: that command is over, whatever else is running.
 *
 * A released manifest whose command has not started is collected, and the
 * command is then refused its start.
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
 * Field 22 of a /proc/PID/stat line, the start time in clock ticks, counted
 * from the last ')' because the comm field can hold spaces and parentheses.
 * `undefined` for a line that is cut short or is not one.
 */
function startTimeFromProcStat(stat: string): string | undefined {
  const comm = stat.lastIndexOf(')')
  const start = stat
    .slice(comm + 1)
    .trim()
    .split(' ')[19]
  return comm > 0 && start !== undefined && /^\d+$/.test(start)
    ? start
    : undefined
}

function processStartTime(pid: number): string | undefined {
  try {
    return startTimeFromProcStat(fs.readFileSync(`/proc/${pid}/stat`, 'utf8'))
  } catch {
    return undefined
  }
}

/**
 * Whether the process with that pid and start time is running. Only "no such
 * process" and a start time that differs say no: a sandboxed command can use up
 * what this user may open, and a /proc that cannot be read must not make a live
 * sandbox's mount points collectable. An unknown `start` leaves the pid alone
 * to go by.
 */
function isRunning(pid: number, start: string): boolean {
  let stat: string
  try {
    stat = fs.readFileSync(`/proc/${pid}/stat`, 'utf8')
  } catch (e) {
    const code = (e as NodeJS.ErrnoException).code
    return code !== 'ENOENT' && code !== 'ESRCH'
  }
  const found = startTimeFromProcStat(stat)
  return found === undefined || !/^\d+$/.test(start) || found === start
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
 * Where processes of this user keep manifests that others can find, in the
 * order tried: under $XDG_RUNTIME_DIR, then under the system temp dir.
 */
function sharedManifestDirectoryNames(): string[] {
  const runtimeDir = process.env['XDG_RUNTIME_DIR']
  const shared =
    runtimeDir !== undefined && path.isAbsolute(runtimeDir)
      ? [path.join(runtimeDir, 'srt-mount-points')]
      : []
  shared.push(
    path.join(tmpdir(), `srt-mount-points-${process.getuid?.() ?? 0}`),
  )
  return shared.filter(candidate => !isBuriedBySandboxMounts(candidate))
}

/**
 * The directory manifests live in: the first shared name that can be made ours
 * alone, else a private directory only this process knows, which keeps the
 * guarantee within this process. Revalidated on every use, because a directory
 * swapped for a symlink between two wraps would send manifests elsewhere.
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
  if (manifestDirectoryUnavailable || isBuriedBySandboxMounts(tmpdir())) {
    return undefined
  }
  try {
    const private_ = fs.mkdtempSync(path.join(tmpdir(), 'srt-mount-points-'))
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
        `[Sandbox Linux] No directory for mount point manifests (${String(e)}) - the mount points this process makes are kept in memory and removed at its own clean-up`,
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
 * Every directory a wrap must bind read-only because some process of this user
 * keeps manifests in it and a collect believes what it finds there: both shared
 * names, plus the one this process settled on.
 *
 * Both names, because a process started without $XDG_RUNTIME_DIR (cron, plain
 * ssh, a service) uses the second, and a sandbox of the first kind with the
 * temp dir writable could otherwise forge its manifests. Each is made if it can
 * be, so a sandboxed command cannot make and fill it first. With `recording`,
 * the directory this wrap's manifest will go to is settled first, so the wrap
 * can pin what lies above it before it publishes.
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

/** What is at a name and is not what this library keeps there. */
class NotOurs extends Error {}

/**
 * What `file` holds, or `undefined` where nothing is there. Only a regular file
 * of the user's, no larger than `max`, is read, through a descriptor opened
 * without following a link and without blocking. Throws {@link NotOurs} for
 * anything else that is there, and the error itself where that cannot be told.
 */
function readOwnFile(file: string, max: number): string | undefined {
  let fd: number
  try {
    fd = fs.openSync(
      file,
      fs.constants.O_RDONLY | fs.constants.O_NOFOLLOW | fs.constants.O_NONBLOCK,
    )
  } catch (e) {
    const code = (e as NodeJS.ErrnoException).code
    if (code === 'ENOENT') return undefined
    // What O_NOFOLLOW says of a link.
    throw code === 'ELOOP' ? new NotOurs(`${file} is a link`) : e
  }
  try {
    const stat = fs.fstatSync(fd)
    if (!stat.isFile() || stat.uid !== process.getuid?.() || stat.size > max) {
      throw new NotOurs(`${file} is not a small regular file of this user's`)
    }
    return fs.readFileSync(fd, 'utf8')
  } finally {
    fs.closeSync(fd)
  }
}

/** `<directory>/<id>` of a manifest, its claim or its started record. */
const idOf = (file: string): string => file.slice(0, file.lastIndexOf('.'))

/**
 * The manifest at `file`, which is its own name or its claim's, or `undefined`
 * where nothing is there. Throws like {@link readOwnFile}, and {@link NotOurs}
 * for what is not a manifest of this version.
 */
function readManifest(file: string): Manifest | undefined {
  const text = readOwnFile(file, MANIFEST_MAX_BYTES)
  if (text === undefined) {
    return undefined
  }
  let json: unknown
  try {
    json = JSON.parse(text)
  } catch {
    throw new NotOurs(`${file} is not JSON`)
  }
  const parsed = ManifestSchema.safeParse(json)
  if (!parsed.success) {
    throw new NotOurs(
      `${file} is not a manifest of version ${MANIFEST_VERSION}`,
    )
  }
  const id = idOf(file)
  return {
    ...parsed.data,
    file,
    claimed: file.endsWith(CLAIMED_SUFFIX),
    record: `${id}${STARTED_SUFFIX}`,
    released: ownManifests.get(`${id}${MANIFEST_SUFFIX}`)?.over === true,
  }
}

/**
 * Whether a process on the started record is running, or `undefined` with no
 * record. A record that cannot be read, is not the user's small regular file,
 * or is not whole /proc/PID/stat lines vouches: only a process that is gone
 * says its sandbox has ended.
 */
function recordVouches(record: string): boolean | undefined {
  let lines: string[]
  try {
    const text = readOwnFile(record, RECORD_MAX_BYTES)
    if (text === undefined) {
      return undefined
    }
    lines = text.split('\n')
  } catch {
    return true
  }
  // Empty between the command line's shell making it and writing to it.
  if (lines.pop() !== '' || lines.length === 0) {
    return true
  }
  return lines.some(line => {
    const pid = /^(\d+) \(/.exec(line)?.[1]
    const start = startTimeFromProcStat(line)
    return (
      pid === undefined || start === undefined || isRunning(Number(pid), start)
    )
  })
}

/**
 * Whether a sandbox that named this manifest may be running, or may yet start.
 * Only a process in the PID namespace that wrote it can tell; to any other it
 * is live, and is collected by a process in its own. With a started record, the
 * record alone says. With none, no sandbox has got past a claim, and one the
 * caller has not released is live while it is young or its writer runs.
 */
function isLive(manifest: Manifest): boolean {
  const here = ownPidNamespace()
  if (here === undefined || manifest.ns !== here) {
    return true
  }
  const vouched = recordVouches(manifest.record)
  if (vouched !== undefined) {
    return vouched
  }
  return (
    !manifest.claimed &&
    !manifest.released &&
    (Date.now() - manifest.created < MANIFEST_GRACE_MS ||
      isRunning(manifest.pid, manifest.start))
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
  /** The manifest, for bubblewrap to bind before it makes a mount point. */
  file: string
  /** Its started record, for the command line to append to before bubblewrap. */
  started: string
}

/**
 * Record the mount points this wrap relies on, and the empty directories they
 * bind from, before the sandbox can start.
 *
 * `undefined` when there is nothing to record or no manifest could be written.
 * What could not be recorded is kept in memory and removed at this process's
 * own clean-up, since no other process will know of it.
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
  if (dir !== undefined) {
    const id = path.join(
      dir,
      `${process.pid}-${randomBytes(8).toString('hex')}`,
    )
    const file = `${id}${MANIFEST_SUFFIX}`
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
    // Written beside the manifest and renamed onto it, so that it is read whole
    // or not at all.
    try {
      fs.writeFileSync(temporary, JSON.stringify(body), { mode: 0o600 })
      fs.renameSync(temporary, file)
      ownManifests.set(file, { commandKey, over: false })
      return { dir, file, started: `${id}${STARTED_SUFFIX}` }
    } catch (e) {
      try {
        fs.unlinkSync(temporary)
      } catch {
        // Never made.
      }
      logForDebugging(
        `[Sandbox Linux] Could not record the mount points this command relies on (${String(e)}) - they are kept in memory and removed at this process's own clean-up`,
        { level: 'warn' },
      )
    }
  }
  for (const mountPoint of mountPoints) unrecorded.paths.add(mountPoint)
  for (const source of sources) unrecorded.sources.add(source)
  return undefined
}

/**
 * Drop the manifest of a wrap that never produced a command. No sandbox can
 * start under it, so the mount points it named are no one's.
 */
export function discardMountPointManifest(file: string): void {
  ownManifests.delete(file)
  drop(file)
}

function drop(file: string): boolean {
  try {
    fs.unlinkSync(file)
    return true
  } catch {
    // Gone already, or not a file.
    return false
  }
}

/** One reading of a manifest directory. */
type Reading = {
  /** Every name in it. */
  names: string[]
  /** The manifests that could be read, claimed ones among them. */
  manifests: Manifest[]
  /**
   * Why a sandbox may be running on paths that this reading cannot list, if one
   * may: nothing may then be removed on it.
   */
  inDoubt?: string
  /** What is there and is of no use to anybody any more. */
  spent: string[]
}

/**
 * Reads the manifests in `dir`, every one that the listing showed.
 *
 * A pass renames a manifest to claim it and to give it back, which can hide it
 * from a listing under way and from the open that follows one. So a listed
 * manifest that is gone when opened starts the reading over, and a started
 * record on which a process runs, with no manifest listed beside it, puts the
 * reading in doubt: a record is never renamed.
 *
 * So does whatever is at a manifest's name and cannot be read: always where
 * that is an error (a sandboxed command can use up what this user may open),
 * and where it is not a manifest of this version, while a process on its record
 * runs or it is younger than {@link UNREADABLE_MANIFEST_MAX_AGE_MS}.
 */
function readManifests(dir: string): Reading {
  const old = (file: string): boolean => {
    try {
      return (
        Date.now() - fs.lstatSync(file).mtimeMs > UNREADABLE_MANIFEST_MAX_AGE_MS
      )
    } catch {
      return false
    }
  }
  for (let attempt = 1; ; attempt++) {
    let names: string[]
    try {
      names = fs.readdirSync(dir)
    } catch (e) {
      return { names: [], manifests: [], spent: [], inDoubt: String(e) }
    }
    const reading: Reading = { names, manifests: [], spent: [] }
    const listed = new Set<string>()
    let moved = false
    for (const name of names) {
      if (!name.endsWith(MANIFEST_SUFFIX) && !name.endsWith(CLAIMED_SUFFIX)) {
        continue
      }
      const file = path.join(dir, name)
      listed.add(idOf(file))
      try {
        const manifest = readManifest(file)
        if (manifest !== undefined) reading.manifests.push(manifest)
        else moved = true
      } catch (e) {
        if (
          e instanceof NotOurs &&
          recordVouches(`${idOf(file)}${STARTED_SUFFIX}`) !== true &&
          old(file)
        ) {
          reading.spent.push(file)
        } else {
          reading.inDoubt ??= `${file}: ${String(e)}`
        }
      }
    }
    if (moved && attempt < LISTING_ATTEMPTS) {
      continue
    }
    if (moved) {
      reading.inDoubt ??= `${dir} kept changing`
    }
    for (const name of names) {
      const file = path.join(dir, name)
      if (name.endsWith(TEMPORARY_SUFFIX)) {
        // Left by a process killed between writing and moving into place.
        if (old(file)) reading.spent.push(file)
      } else if (name.endsWith(STARTED_SUFFIX) && !listed.has(idOf(file))) {
        if (recordVouches(file) === true) {
          reading.inDoubt ??= `${file} has no manifest`
        } else {
          reading.spent.push(file)
        }
      }
    }
    return reading
  }
}

/**
 * The mount points the manifests name, on one reading of the directory: `live`
 * by a manifest whose sandbox may still be running, `named` by any manifest, a
 * claimed one included. What only a finished manifest names is a leftover the
 * next pass removes.
 *
 * With no directory, or none that can be read, both hold only what this process
 * could record nowhere: a wrap takes a path for a mount point on a manifest's
 * word only, so it then takes every other existing path for the caller's own.
 */
export function namedMountPoints(): { live: Set<string>; named: Set<string> } {
  const live = new Set(unrecorded.paths)
  const named = new Set(unrecorded.paths)
  const dir = onLinux() ? ensureManifestDirectory() : undefined
  for (const manifest of dir === undefined
    ? []
    : readManifests(dir).manifests) {
    const isLiveOne = isLive(manifest)
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
 * The directory this process keeps its manifests in, if it exists already.
 * Makes and settles nothing: for a look that must leave the host as found.
 */
function existingManifestDirectory(): string | undefined {
  return manifestDirectory !== undefined &&
    isOurPrivateDirectory(manifestDirectory)
    ? manifestDirectory
    : sharedManifestDirectoryNames().find(isOurPrivateDirectory)
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
 * A snapshot that may be out of date by the time the caller acts. Its only safe
 * use is to SKIP a removal; a path not being in it never means the path is free
 * to write.
 *
 * A path is in the set only when both hold:
 *
 * - a manifest names it, and that manifest is live by the clean-up's rule, or
 *   something in the directory cannot be read and may have a sandbox under it,
 *   in which case every named path counts;
 * - what is at the path now is still an empty placeholder: an empty regular
 *   file with no write bit and one link, or an empty directory, and the user's.
 *   So a stale or forged manifest never makes a caller spare a file with
 *   content.
 *
 * Paths are as the wraps recorded them: absolute, links above the last
 * component resolved. It answers for one manifest directory, the one this
 * process uses or, before its first wrap, the first shared name that exists, so
 * a sandbox whose process keeps manifests elsewhere is not seen. Makes nothing
 * on the host. Empty off Linux and where no manifest directory exists.
 */
export function liveMountPoints(): ReadonlySet<string> {
  const spared = new Set<string>()
  if (!onLinux()) {
    return spared
  }
  const dir = existingManifestDirectory()
  const reading = dir === undefined ? undefined : readManifests(dir)
  const named = new Set(unrecorded.paths)
  for (const manifest of reading?.manifests ?? []) {
    if (reading?.inDoubt !== undefined || isLive(manifest)) {
      for (const mountPoint of manifest.paths) named.add(mountPoint)
    }
  }
  for (const mountPoint of named) {
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
  const dir = ensureManifestDirectory()
  if (dir !== undefined) {
    return collect(dir, release === 'all')
  }
  const removed: string[] = []
  if (release === 'all') {
    for (const mountPoint of unrecorded.paths) {
      if (removeMountPoint(mountPoint) === 'removed') removed.push(mountPoint)
    }
    for (const source of unrecorded.sources) {
      if (removeMountSource(source) === 'removed') removed.push(source)
    }
    unrecorded.paths.clear()
    unrecorded.sources.clear()
  }
  return removed
}

/**
 * One pass over a manifest directory. It takes no lock and waits for nothing;
 * any number may run at once, over the same claims.
 *
 * INVARIANT: a path is removed only when every manifest that names it is
 * claimed and has no process on its record, by a reading made after the claims.
 * bubblewrap binds the manifest before it makes a mount point, so a start under
 * a claimed manifest is refused, and a sandbox that got past the claim wrote
 * its record first: every reading after the claim finds it. A manifest at its
 * own name keeps what it names, live or not, since a start under it can succeed
 * at any moment. Acting on a reading made before the claims would remove a
 * mount point from under a sandbox that started in between.
 *
 * A pass gives back the claims it made itself, and only when that reading finds
 * a process on the record. So what remains is a manifest that comes to its own
 * name after the reading, published or given back, whose sandbox reaches its
 * bind on a path a claimed manifest names too. The directory is listed again
 * before every removal (in a pass of over {@link
 * LISTS_BEFORE_EACH_REMOVAL_UP_TO} candidates, whenever the listing is {@link
 * LISTING_GOOD_FOR_MS} old), and what has come to its name keeps what it names,
 * so the pass would have to be held up between a listing and the removal that
 * follows it for as long as a sandbox takes to start.
 *
 * A manifest is all that names its mount points, so its claim is dropped last,
 * and stays, for a later pass, when the pass turns back or a removal is refused.
 */
function collect(dir: string, unrecordedToo: boolean): string[] {
  const before = readManifests(dir)
  before.spent.forEach(drop)
  const own = new Set<string>()
  let claims = false
  if (before.inDoubt === undefined) {
    // Forget own manifests that something else has removed.
    const there = new Set(before.names.map(name => idOf(path.join(dir, name))))
    for (const file of ownManifests.keys()) {
      if (path.dirname(file) === dir && !there.has(idOf(file))) {
        ownManifests.delete(file)
      }
    }
    for (const manifest of before.manifests) {
      if (!manifest.claimed && !isLive(manifest)) {
        const claim = `${idOf(manifest.file)}${CLAIMED_SUFFIX}`
        try {
          fs.renameSync(manifest.file, claim)
          own.add(claim)
        } catch {
          // Another pass has it.
        }
      }
      claims ||= manifest.claimed || own.size > 0
    }
  }
  const reading = claims ? readManifests(dir) : before
  if (reading.inDoubt !== undefined) {
    logForDebugging(
      `[Sandbox Linux] A sandbox may be running on mount points that cannot be listed - leaving every mount point where it is (${reading.inDoubt})`,
      { level: 'warn' },
    )
    return []
  }

  const kept = new Set<string>()
  const keep = (manifest: Manifest): void => {
    for (const named of [...manifest.paths, ...manifest.sources]) {
      kept.add(named)
    }
  }
  const finished: Manifest[] = []
  for (const manifest of reading.manifests) {
    if (manifest.claimed && !isLive(manifest)) {
      finished.push(manifest)
      continue
    }
    keep(manifest)
    if (own.has(manifest.file)) {
      try {
        fs.renameSync(manifest.file, `${idOf(manifest.file)}${MANIFEST_SUFFIX}`)
      } catch {
        // Stays claimed, and kept while a process on its record runs.
      }
    }
  }

  // Each path once, and as a mount point where a manifest names it as one.
  const candidates = new Map<string, boolean>()
  for (const manifest of unrecordedToo ? [...finished, unrecorded] : finished) {
    for (const mountPoint of manifest.paths) {
      candidates.set(mountPoint, false)
    }
    for (const source of manifest.sources) {
      if (!candidates.has(source)) {
        candidates.set(source, true)
      }
    }
  }
  const known = new Set(reading.names)
  const goodFor =
    candidates.size <= LISTS_BEFORE_EACH_REMOVAL_UP_TO ? 0 : LISTING_GOOD_FOR_MS
  let listedAt = -Infinity
  const newcomersKeepWhatTheyName = (): boolean => {
    try {
      for (const name of fs.readdirSync(dir)) {
        if (known.has(name) || !name.endsWith(MANIFEST_SUFFIX)) continue
        // Published, or given back, since the reading. One that is gone again
        // is looked for the next time: it may be given back once more.
        const arrived = readManifest(path.join(dir, name))
        if (arrived === undefined) continue
        keep(arrived)
        known.add(name)
      }
    } catch (e) {
      logForDebugging(
        `[Sandbox Linux] The mount point manifests could not be read again (${String(e)}) - leaving the rest where it is`,
        { level: 'warn' },
      )
      return false
    }
    listedAt = performance.now()
    return true
  }

  const removed: string[] = []
  const notRemoved = new Set<string>()
  for (const [candidate, isSource] of candidates) {
    if (
      performance.now() - listedAt >= goodFor &&
      !newcomersKeepWhatTheyName()
    ) {
      return removed
    }
    if (kept.has(candidate)) {
      continue
    }
    const outcome = isSource
      ? removeMountSource(candidate)
      : removeMountPoint(candidate)
    if (outcome === 'removed') {
      removed.push(candidate)
    } else if (outcome === 'failed') {
      notRemoved.add(candidate)
    }
  }
  if (unrecordedToo) {
    for (const named of [unrecorded.paths, unrecorded.sources]) {
      for (const one of named) if (!notRemoved.has(one)) named.delete(one)
    }
  }
  for (const manifest of finished) {
    // A mount point that could not be removed from here is still somebody's to
    // remove, and the manifest is all that says so. The record goes only with
    // the claim: a manifest given back since may have a sandbox on its record.
    if (
      ![...manifest.paths, ...manifest.sources].some(named =>
        notRemoved.has(named),
      ) &&
      drop(manifest.file)
    ) {
      drop(manifest.record)
      ownManifests.delete(`${idOf(manifest.file)}${MANIFEST_SUFFIX}`)
    }
  }
  return removed
}

/**
 * Forget which directory the manifests are kept in, so the next use works it
 * out again from the environment. Test seam: a test gives itself a runtime
 * directory of its own after this module may have settled on the real one.
 */
export function forgetMountPointManifestDirectory(): void {
  manifestDirectory = undefined
  manifestDirectoryIsPrivate = false
  manifestDirectoryUnavailable = false
  directoryFailureLogged = false
}
