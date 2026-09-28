import { describe, it, expect, beforeEach, afterEach, spyOn } from 'bun:test'
import { spawn, spawnSync } from 'node:child_process'
import * as fs from 'node:fs'
import {
  accessSync,
  chmodSync,
  constants,
  existsSync,
  linkSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  realpathSync,
  renameSync,
  rmSync,
  statSync,
  statfsSync,
  symlinkSync,
  utimesSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { basename, dirname, join } from 'node:path'
import {
  type ManifestDirectoryPlaces,
  collectMountPoints,
  liveMountPoints,
  mountPointManifestDirectories,
  namedMountPoints,
  publishMountPointManifest,
  setMountPointManifestPlacesForTesting,
} from '../../src/sandbox/bwrap-mount-manifests.js'
import { bwrapCanNamespace } from '../helpers/bwrap-namespace.js'
import { isLinux } from '../helpers/platform.js'
import { usePrivateManifestDirectory } from '../helpers/private-manifest-directory.js'

/**
 * The manifests and the pass that collects on their word, below the level of a
 * sandbox: what a pass believes, what it looks at again before it removes
 * anything, and that the directory's lock neither holds a process up nor is
 * relied on.
 */
describe.if(isLinux)('The mount point manifests', () => {
  const runtime = usePrivateManifestDirectory()
  const MODULE = join(
    import.meta.dir,
    '../../src/sandbox/bwrap-mount-manifests.ts',
  )
  const LIBRARY = JSON.stringify(
    join(import.meta.dir, '../../src/sandbox/linux-sandbox-utils.ts'),
  )
  const BWRAP_CAN_NAMESPACE = bwrapCanNamespace()
  const NOT_ROOT = process.getuid?.() !== 0
  const OWN_NAMESPACE = isLinux ? readlinkSync('/proc/self/ns/pid') : ''

  let BASE: string
  let DIR: string // where the manifests go
  let LOCK: string // the directory's lock
  let X: string // a mount point an earlier sandbox left
  let TMP: string // the temp dir of every child process
  let THEIRS: string // the directory under /tmp, which this process only reads

  beforeEach(() => {
    BASE = realpathSync(mkdtempSync(join(tmpdir(), 'mount-point-manifests-')))
    TMP = join(BASE, 'tmp')
    mkdirSync(TMP)
    DIR = runtime.manifestDir()
    mkdirSync(DIR, { recursive: true, mode: 0o700 })
    chmodSync(DIR, 0o700)
    LOCK = join(DIR, 'directory.lock')
    X = join(BASE, 'config.lock')
    THEIRS = join(
      runtime.places().tempDir,
      `srt-mount-points-${process.getuid!()}`,
    )
  })

  afterEach(() => {
    try {
      chmodSync(THEIRS, 0o700)
    } catch {
      // Not made by this test.
    }
    rmSync(THEIRS, { recursive: true, force: true })
    for (const name of readdirSync(DIR)) {
      const file = join(DIR, name)
      try {
        chmodSync(file, 0o700)
      } catch {
        // A dangling link.
      }
      rmSync(file, { recursive: true, force: true })
    }
    collectMountPoints()
    rmSync(BASE, { recursive: true, force: true })
  })

  /** What bubblewrap leaves on the host for `--ro-bind /dev/null <absent>`. */
  function leftover(p: string): void {
    writeFileSync(p, '')
    chmodSync(p, 0o444)
  }

  /** A pid nothing in this PID namespace has. */
  function deadPid(): number {
    for (let pid = 4194000; pid > 1; pid--) {
      if (!existsSync(`/proc/${pid}`)) return pid
    }
    throw new Error('no free pid')
  }

  /**
   * The manifest of a wrap whose process is gone and which is long past its
   * grace: what a killed process leaves. `fields` overrides what it says.
   */
  function manifestOfADeadProcess(
    paths: string[],
    fields: Record<string, unknown> = {},
    dir = DIR,
  ): string {
    const pid = deadPid()
    const file = join(dir, `${pid}-${Math.random().toString(16).slice(2)}.json`)
    const body: Record<string, unknown> = {
      version: 1,
      pid,
      start: '1',
      ns: OWN_NAMESPACE,
      created: Date.now() - 60_000,
      paths,
      sources: [],
      ...fields,
    }
    for (const [key, value] of Object.entries(body)) {
      if (value === undefined) delete body[key]
    }
    writeFileSync(file, JSON.stringify(body), { mode: 0o600 })
    return file
  }

  /**
   * Runs `source` with the module as `m` in a process of its own, which is
   * killed if it does not end by itself: what these cases guard against blocks
   * the thread. `first` runs before the module is loaded, and an `env` entry
   * that is undefined is removed from the child's environment.
   *
   * The child looks where this process does for the runtime directory and has a
   * temp dir of its own, which also stands in for `/tmp`. `places` puts
   * something else in the place of either. It has no `XDG_RUNTIME_DIR` unless
   * `env` gives it one.
   */
  function inAChild(
    source: string,
    options: {
      launcher?: string[]
      env?: Record<string, string | undefined>
      first?: string
      places?: Partial<ManifestDirectoryPlaces>
    } = {},
  ): { status: number | null; ms: number; stdout: string } {
    const script = writeChild(
      `child-${Math.random().toString(16).slice(2)}.ts`,
      source,
      options.places,
      options.first,
    )
    const argv = [...(options.launcher ?? []), process.execPath, script]
    const began = Date.now()
    const run = spawnSync(argv[0]!, argv.slice(1), {
      env: childEnv(options.env),
      encoding: 'utf8',
      timeout: 6000,
      killSignal: 'SIGKILL',
    })
    return { status: run.status, ms: Date.now() - began, stdout: run.stdout }
  }

  /** The script {@link inAChild} runs, for a child that is started otherwise. */
  function writeChild(
    name: string,
    source: string,
    places: Partial<ManifestDirectoryPlaces> = {},
    first = '',
  ): string {
    const script = join(BASE, name)
    const module = runtime.isolated(MODULE, {
      runtimeDir: runtime.places().runtimeDir,
      tempDir: TMP,
      ...places,
    })
    writeFileSync(
      script,
      `${first}\nconst m = await import(${JSON.stringify(module)})\n${source}\n`,
    )
    return script
  }

  /** The environment {@link inAChild} gives its child. */
  function childEnv(
    given: Record<string, string | undefined> = {},
  ): Record<string, string> {
    const env: Record<string, string | undefined> = {
      ...process.env,
      XDG_RUNTIME_DIR: undefined,
      TMPDIR: TMP,
      ...given,
    }
    for (const [name, value] of Object.entries(env)) {
      if (value === undefined) delete env[name]
    }
    return env as Record<string, string>
  }

  const COLLECT = `m.collectMountPoints()`
  const PUBLISH = `console.log(JSON.stringify(m.publishMountPointManifest(['/nonexistent/x'], []) ?? null))`

  // ---- the directory's lock never holds a process up ----
  //
  // Whatever is at the lock's name, a collect and a publish both come back: by
  // the deadline when it is somebody's lock, and at once when it is nothing
  // this process could ever take. "At once" is held to well under the
  // two-second wait, which one command makes four times over.
  const AT_ONCE_MS = 1500

  const notALock: [string, () => void, boolean][] = [
    ['a directory', () => mkdirSync(LOCK), true],
    [
      'a FIFO nobody writes to',
      () => expect(spawnSync('mkfifo', [LOCK]).status).toBe(0),
      true,
    ],
    [
      'a link to nothing',
      () => symlinkSync(join(BASE, 'nothing-here'), LOCK),
      true,
    ],
    [
      'a file that cannot be read',
      () => {
        writeFileSync(LOCK, `${deadPid()} 1 ${OWN_NAMESPACE}\n`)
        chmodSync(LOCK, 0o000)
      },
      NOT_ROOT,
    ],
  ]
  for (const [what, plant, applies] of notALock) {
    it.if(applies)(
      `comes back from a collect when its lock is ${what}`,
      () => {
        plant()
        const collected = inAChild(COLLECT)
        expect(collected.status).toBe(0)
        expect(collected.ms).toBeLessThan(AT_ONCE_MS)
      },
      15000,
    )

    it.if(applies)(
      `records a wrap's mount points all the same when its lock is ${what}`,
      () => {
        plant()
        const published = inAChild(PUBLISH)
        expect(published.status).toBe(0)
        expect(published.ms).toBeLessThan(AT_ONCE_MS)
        // A wrap is not refused, nor left unrecorded, for want of the lock.
        const manifest = JSON.parse(published.stdout) as { file: string }
        expect(readFileSync(manifest.file, 'utf8')).toContain('/nonexistent/x')
      },
      15000,
    )
  }

  it.if(BWRAP_CAN_NAMESPACE && NOT_ROOT)(
    'comes back from a collect at once where the directory is read-only from here, and collects nothing on its word',
    () => {
      // What a process inside a sandbox sees of the directory: bound read-only,
      // with a lock in it that it could never remove. It keeps its own
      // manifests elsewhere and does not judge what is in this one.
      const lock = `${deadPid()} 1 ${OWN_NAMESPACE}\n`
      writeFileSync(LOCK, lock)
      leftover(X)
      const manifest = manifestOfADeadProcess([X])
      const collected = inAChild(COLLECT, {
        launcher: [
          'bwrap',
          '--dev-bind',
          '/',
          '/',
          '--ro-bind',
          DIR,
          DIR,
          '--',
        ],
      })
      expect(collected.status).toBe(0)
      expect(collected.ms).toBeLessThan(AT_ONCE_MS)
      expect(readFileSync(LOCK, 'utf8')).toBe(lock)
      expect(existsSync(X)).toBe(true)
      expect(existsSync(manifest)).toBe(true)
    },
    15000,
  )

  it('waits for a lock somebody holds, and no longer than the wait', () => {
    // This process, which is running, in this namespace.
    const start = readFileSync('/proc/self/stat', 'utf8')
      .split(') ')
      .pop()!
      .split(' ')[19]
    writeFileSync(LOCK, `${process.pid} ${start} ${OWN_NAMESPACE}\n`)
    leftover(X)
    manifestOfADeadProcess([X])

    const collected = inAChild(COLLECT)
    expect(collected.status).toBe(0)
    expect(collected.ms).toBeGreaterThan(1500)
    expect(collected.ms).toBeLessThan(5500)
    // The pass was left to the holder: nothing was removed, its lock stands.
    expect(existsSync(X)).toBe(true)
    expect(readFileSync(LOCK, 'utf8')).toContain(`${process.pid} `)
  }, 15000)

  it('believes a lock that names nobody until it is old, and breaks it then', () => {
    // An empty lock file says nothing about its holder. It is believed like any
    // other lock whose holder cannot be asked after, not taken for nobody's and
    // removed.
    writeFileSync(LOCK, '')
    leftover(X)
    manifestOfADeadProcess([X])

    const young = inAChild(COLLECT)
    expect(young.status).toBe(0)
    expect(young.ms).toBeGreaterThan(1500)
    expect(existsSync(LOCK)).toBe(true)
    expect(existsSync(X)).toBe(true)

    const longAgo = new Date(Date.now() - 61_000)
    utimesSync(LOCK, longAgo, longAgo)
    const old = inAChild(COLLECT)
    expect(old.status).toBe(0)
    expect(old.ms).toBeLessThan(4000)
    expect(existsSync(LOCK)).toBe(false)
    expect(existsSync(X)).toBe(false)
  }, 20000)

  it('breaks at once the lock of a holder in this namespace that is gone, and not one from another namespace', () => {
    leftover(X)
    manifestOfADeadProcess([X])

    // Its pid is no process here, which says nothing about a holder whose pid
    // was given in another namespace.
    writeFileSync(LOCK, `${deadPid()} 1 pid:[1]\n`)
    const elsewhere = inAChild(COLLECT)
    expect(elsewhere.status).toBe(0)
    expect(elsewhere.ms).toBeGreaterThan(1500)
    expect(existsSync(X)).toBe(true)

    writeFileSync(LOCK, `${deadPid()} 1 ${OWN_NAMESPACE}\n`)
    const here = inAChild(COLLECT)
    expect(here.status).toBe(0)
    // The pass ran, which it does not after waiting in vain.
    expect(existsSync(X)).toBe(false)
    expect(existsSync(LOCK)).toBe(false)
  }, 20000)

  // ---- nothing rests on the lock -----------------------------------------

  /**
   * Runs `during` once, in the middle of the next pass: after it has listed
   * the manifests and decided what is finished, before it removes anything.
   */
  function duringTheNextPass(during: () => void): { restore(): void } {
    const readFile = fs.readFileSync
    let done = false
    const spy = spyOn(fs, 'readFileSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      if (file === '/proc/locks' && !done) {
        done = true
        during()
      }
      return (readFile as (f: unknown, o: unknown) => unknown)(file, options)
    }) as never)
    return { restore: () => spy.mockRestore() }
  }

  it('removes what a finished manifest names once nothing else names it', () => {
    leftover(X)
    const manifest = manifestOfADeadProcess([X])
    expect(collectMountPoints()).toEqual([X])
    expect(existsSync(X)).toBe(false)
    expect(existsSync(manifest)).toBe(false)
  })

  it('keeps a mount point named by a manifest that is published while the pass is under way', () => {
    // The lock does not exclude, so a manifest can appear between a pass
    // listing the directory and its removals, naming a path the pass is about
    // to remove, with a sandbox starting under it.
    leftover(X)
    manifestOfADeadProcess([X])
    let published: { status: number | null; stdout: string } | undefined
    const pass = duringTheNextPass(() => {
      rmSync(LOCK, { force: true }) // what a waiter breaking the lock does
      published = inAChild(
        `console.log(JSON.stringify(m.publishMountPointManifest([${JSON.stringify(X)}], []) ?? null))`,
      )
    })
    let removed: string[]
    try {
      removed = collectMountPoints()
    } finally {
      pass.restore()
    }
    expect(published?.status).toBe(0)
    const arrived = (JSON.parse(published!.stdout) as { file: string }).file
    expect(readFileSync(arrived, 'utf8')).toContain(X)
    expect(removed).toEqual([])
    expect(existsSync(X)).toBe(true)
  }, 15000)

  it('gives up only a lock that is still its own', () => {
    // Held up for longer than a lock is believed, a pass finds on its way out
    // that the lock at that name is somebody else's by now, and must leave it.
    const theirs = `${process.ppid} 1 pid:[1]\n`
    let mine = ''
    const pass = duringTheNextPass(() => {
      mine = readFileSync(LOCK, 'utf8')
      rmSync(LOCK)
      writeFileSync(LOCK, theirs)
    })
    try {
      collectMountPoints()
    } finally {
      pass.restore()
    }
    // Whole while it was held: who, since when, and where that can be asked.
    expect(mine).toMatch(
      new RegExp(
        `^${process.pid} \\d+ ${OWN_NAMESPACE.replace(/[[\]]/g, '\\$&')}\n$`,
      ),
    )
    expect(readFileSync(LOCK, 'utf8')).toBe(theirs)
  })

  it('makes its lock whole: it is never there with nothing in it', () => {
    // Linked into place from a file already written, so that nobody who finds
    // it can find it empty.
    const linked: string[] = []
    const link = fs.linkSync
    const spy = spyOn(fs, 'linkSync').mockImplementation(((
      from: string,
      to: string,
    ) => {
      if (to === LOCK) linked.push(readFileSync(from, 'utf8'))
      return link(from, to)
    }) as never)
    try {
      collectMountPoints()
    } finally {
      spy.mockRestore()
    }
    expect(linked.length).toBe(1)
    expect(linked[0]).toMatch(/^\d+ \d+ \S+\n$/)
    // And nothing of the making is left behind.
    expect(readdirSync(DIR)).toEqual([])
  })

  it('looks at /proc/locks a bounded number of times, not once for every mount point', () => {
    // The list is the host's: reading all of it for each removal would make a
    // pass over many mount points outlast the lock's waiters.
    const many = 500
    const paths: string[] = []
    for (let i = 0; i < many; i++) {
      const p = join(BASE, `.placeholder-${i}`)
      leftover(p)
      paths.push(p)
    }
    expect(publishMountPointManifest(paths, [])).toBeDefined()
    const spy = spyOn(fs, 'readFileSync')
    let removed: string[]
    let looks: number
    let tookMs: number
    try {
      const began = Date.now()
      removed = collectMountPoints()
      tookMs = Date.now() - began
      looks = spy.mock.calls.filter(([file]) => file === '/proc/locks').length
    } finally {
      spy.mockRestore()
    }
    expect(removed.length).toBe(many)
    // One to begin with, one before the first removal, one for every 64
    // removals after that, and one more for every two milliseconds the pass
    // took. No fewer either: one look is not good for ever.
    expect(looks).toBeGreaterThanOrEqual(1 + Math.ceil(many / 64))
    expect(looks).toBeLessThanOrEqual(
      3 + Math.ceil(many / 64) + Math.ceil(tookMs / 2),
    )
    expect(looks).toBeLessThan(many)
  })

  it.if(NOT_ROOT)(
    'keeps the manifest of a mount point it could not remove, for a pass that can',
    () => {
      // Seen read-only from here, as from inside a sandbox that may not write
      // the directory it is in. The manifest is all that says the file is a
      // mount point, so it must stay while the file does.
      const readOnly = join(BASE, 'read-only-from-here')
      mkdirSync(readOnly)
      const inside = join(readOnly, 'config.lock')
      leftover(inside)
      const manifest = manifestOfADeadProcess([inside])
      chmodSync(readOnly, 0o555)
      try {
        expect(collectMountPoints()).toEqual([])
        expect(existsSync(inside)).toBe(true)
        expect(existsSync(manifest)).toBe(true)
      } finally {
        chmodSync(readOnly, 0o755)
      }
      expect(collectMountPoints()).toEqual([inside])
      expect(existsSync(manifest)).toBe(false)
    },
  )

  // ---- a manifest goes last, this process's own like anybody's ----
  //
  // A manifest is all that names its mount points. It stays until a pass has
  // removed what it names: after a pass that turned back, or a removal that was
  // refused, a later pass still has it to go by.

  it.if(NOT_ROOT)(
    'keeps the manifest of a wrap of its own whose mount point it could not remove, for a pass that can',
    () => {
      const readOnly = join(BASE, 'read-only-from-here')
      mkdirSync(readOnly)
      const inside = join(readOnly, 'config.lock')
      leftover(inside)
      const manifest = publishMountPointManifest([inside], [])!.file
      chmodSync(readOnly, 0o555)
      try {
        expect(collectMountPoints('all')).toEqual([])
        expect(existsSync(inside)).toBe(true)
        expect(existsSync(manifest)).toBe(true)
      } finally {
        chmodSync(readOnly, 0o755)
      }
      // Whatever the next pass is told to release: that this wrap is over has
      // been said already.
      expect(collectMountPoints('none')).toEqual([inside])
      expect(existsSync(manifest)).toBe(false)
    },
  )

  it('keeps the manifest of a wrap of its own when the pass turns back half way, for the next', () => {
    leftover(X)
    const manifest = publishMountPointManifest([X], [])!.file
    // Another version of this library publishes, in a layout this one cannot
    // read, after the pass has listed the directory: the pass stops short of
    // removing anything.
    const stranger = join(DIR, '4242-0123456789abcdef.json')
    const pass = duringTheNextPass(() =>
      writeFileSync(stranger, '{"version":2}'),
    )
    try {
      expect(collectMountPoints('all')).toEqual([])
    } finally {
      pass.restore()
    }
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)

    rmSync(stranger)
    expect(collectMountPoints('none')).toEqual([X])
    expect(existsSync(manifest)).toBe(false)
  })

  it('turns back, keeping everything, at an unreadable manifest that may have a sandbox starting under it', () => {
    leftover(X)
    const theirs = manifestOfADeadProcess([X])
    const own = publishMountPointManifest([join(BASE, 'other')], [])!.file
    const stranger = join(DIR, '1-garbage.json')
    writeFileSync(stranger, '{ not json')
    expect(collectMountPoints('all')).toEqual([])
    expect(existsSync(X)).toBe(true)
    expect(existsSync(theirs)).toBe(true)
    expect(existsSync(own)).toBe(true)
    // Once it is old enough that nothing can be starting under it, and no
    // lock is on it, it stands in the way of nothing.
    const halfAMinuteAgo = new Date(Date.now() - 30_000)
    utimesSync(stranger, halfAMinuteAgo, halfAMinuteAgo)
    expect(collectMountPoints('none')).toEqual([X])
    expect(existsSync(own)).toBe(false)
    expect(existsSync(stranger)).toBe(true)
  })

  it('removes nothing when /proc/locks cannot be read', () => {
    leftover(X)
    const manifest = manifestOfADeadProcess([X])
    const readFile = fs.readFileSync
    const spy = spyOn(fs, 'readFileSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      if (file === '/proc/locks') {
        throw Object.assign(new Error('EACCES: /proc/locks'), {
          code: 'EACCES',
        })
      }
      return (readFile as (f: unknown, o: unknown) => unknown)(file, options)
    }) as never)
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)
  })

  it('keeps what a finished manifest names when its lock shows on the look before the removals', () => {
    // The bubblewrap a wrap has handed to its caller takes its lock whenever
    // the caller starts it, so the kernel is asked again before anything goes.
    leftover(X)
    const manifest = manifestOfADeadProcess([X])
    const line = `1: POSIX  ADVISORY  READ 4242 ${deviceOf(manifest)}:${statSync(manifest).ino} 0 EOF\n`
    const readFile = fs.readFileSync
    let reads = 0
    const spy = spyOn(fs, 'readFileSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      if (file === '/proc/locks') {
        reads++
        return reads === 1 ? '' : line
      }
      return (readFile as (f: unknown, o: unknown) => unknown)(file, options)
    }) as never)
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      spy.mockRestore()
    }
    expect(reads).toBeGreaterThan(1)
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)
  })

  it('lists the directory again between removals, not only before the first', () => {
    // A sandbox about to start on a path shows as a manifest that was not there
    // when the pass began, at any point of a pass over many mount points. One
    // listing is good for a quarter of a millisecond.
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    manifestOfADeadProcess([X, Y])
    const unlink = fs.unlinkSync
    let arrived: string | undefined
    const spy = spyOn(fs, 'unlinkSync').mockImplementation(((file: string) => {
      unlink(file)
      if (file === X && arrived === undefined) {
        // Published the moment the first mount point has gone, with the pass
        // held up for a millisecond before the next: less than the two for
        // which it trusts what it read from /proc/locks.
        arrived = manifestOfADeadProcess([Y], {
          pid: process.pid,
          created: Date.now(),
        })
        Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, 1)
      }
    }) as never)
    let removed: string[]
    try {
      removed = collectMountPoints()
    } finally {
      spy.mockRestore()
    }
    expect(arrived).toBeDefined()
    expect(removed).toEqual([X])
    expect(existsSync(Y)).toBe(true)
  })

  it('is live for half a second from when it was written, though its writer is gone', () => {
    // bubblewrap takes the lock in the sandbox's init process, a moment after
    // a wrapping process killed just then could still have vouched for it.
    leftover(X)
    const manifest = manifestOfADeadProcess([X], { created: Date.now() })
    expect(collectMountPoints()).toEqual([])
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)
  })

  // ---- a manifest is only a claim about a path ---------------------------

  it('leaves what a finished manifest names when it no longer looks like a mount point', () => {
    const written = join(BASE, 'written-to')
    writeFileSync(written, 'mine')
    chmodSync(written, 0o444)
    const writable = join(BASE, 'writable')
    writeFileSync(writable, '')
    chmodSync(writable, 0o644)
    const linked = join(BASE, 'linked')
    leftover(linked)
    linkSync(linked, join(BASE, 'linked-again'))
    const pointer = join(BASE, 'pointer')
    leftover(join(BASE, 'pointed-at'))
    symlinkSync(join(BASE, 'pointed-at'), pointer)
    const inUse = join(BASE, 'directory-in-use')
    mkdirSync(inUse)
    writeFileSync(join(inUse, 'file'), '')
    const manifest = manifestOfADeadProcess([
      written,
      writable,
      linked,
      pointer,
      inUse,
    ])
    expect(collectMountPoints()).toEqual([])
    for (const kept of [written, writable, linked, pointer, inUse]) {
      expect(existsSync(kept)).toBe(true)
    }
    expect(existsSync(join(BASE, 'pointed-at'))).toBe(true)
    // None of them is a mount point any more, so the manifest has nothing
    // left to say.
    expect(existsSync(manifest)).toBe(false)
  })

  it("leaves a file, and an empty directory, that is somebody else's", () => {
    const directory = join(BASE, 'empty-directory')
    leftover(X)
    mkdirSync(directory)
    manifestOfADeadProcess([X, directory])
    // As another user's would look: nothing here can make one.
    const lstat = fs.lstatSync
    const spy = spyOn(fs, 'lstatSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      const stat = (lstat as (f: unknown, o: unknown) => fs.Stats)(
        file,
        options,
      )
      if (file === X || file === directory) {
        const theirs = Object.create(Object.getPrototypeOf(stat)) as fs.Stats
        return Object.assign(theirs, stat, { uid: stat.uid + 1 })
      }
      return stat
    }) as never)
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(X)).toBe(true)
    expect(existsSync(directory)).toBe(true)
  })

  it('takes away what a killed process left half written, once it is old', () => {
    const old = [
      join(DIR, 'directory.lock.4242.0123456789abcdef.tmp'),
      join(DIR, '4242-0123456789abcdef.json.tmp'),
    ]
    const young = join(DIR, '4243-0123456789abcdef.json.tmp')
    for (const file of [...old, young]) writeFileSync(file, '{}')
    const hoursAgo = new Date(Date.now() - 2 * 3600 * 1000)
    for (const file of old) utimesSync(file, hoursAgo, hoursAgo)
    collectMountPoints()
    for (const file of old) expect(existsSync(file)).toBe(false)
    // This one may be on its way into place.
    expect(existsSync(young)).toBe(true)
  })

  // ---- liveness is relative to a PID namespace ----
  //
  // /proc/locks lists a lock only when its holder has a pid in the namespace of
  // the /proc being read, and /proc/PID is local to it. From another namespace
  // a running sandbox's manifest looks like one a dead process left.

  it.each([
    ['written in another PID namespace', 'kept', { ns: 'pid:[1]' }],
    [
      'written in another PID namespace a long time ago',
      'kept',
      { ns: 'pid:[1]', created: Date.now() - 7 * 24 * 3600 * 1000 },
    ],
    ['that does not say where it was written', 'kept', { ns: undefined }],
    [
      'that does not say where it was written, from hours ago',
      'collected',
      { ns: undefined, created: Date.now() - 2 * 3600 * 1000 },
    ],
    ['written in this PID namespace', 'collected', {}],
  ] as const)(
    'a manifest %s, with no writer and no lock to be seen, is %s',
    (_what, outcome, fields) => {
      leftover(X)
      const manifest = manifestOfADeadProcess([X], fields)
      collectMountPoints()
      expect(existsSync(X)).toBe(outcome === 'kept')
      expect(existsSync(manifest)).toBe(outcome === 'kept')
    },
  )

  // ---- an inode number is not a file -------------------------------------

  /** Has the next passes read `text` for /proc/locks. */
  function withProcLocks(text: string): { restore(): void } {
    const readFile = fs.readFileSync
    const spy = spyOn(fs, 'readFileSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) =>
      file === '/proc/locks'
        ? text
        : (readFile as (f: unknown, o: unknown) => unknown)(
            file,
            options,
          )) as never)
    return { restore: () => spy.mockRestore() }
  }

  /** `major:minor` of the filesystem `p` is on, as /proc/locks prints it. */
  function deviceOf(p: string): string {
    const dev = statSync(p, { bigint: true }).dev
    const major = ((dev >> 8n) & 0xfffn) | ((dev >> 32n) & ~0xfffn)
    const minor = (dev & 0xffn) | ((dev >> 12n) & ~0xffn)
    const hex = (n: bigint): string => n.toString(16).padStart(2, '0')
    return `${hex(major)}:${hex(minor)}`
  }

  // tmpfs, ext2/3/4 and xfs report for a file the device /proc/locks prints.
  const DEVICES_COMPARE =
    isLinux &&
    [0x01021994, 0xef53, 0x58465342].includes(
      Number(statfsSync(realpathSync(tmpdir())).type),
    )

  it.if(DEVICES_COMPARE)(
    'is not kept live by a lock on a file with the same inode number on another filesystem',
    () => {
      // Inode numbers are per filesystem, and on a young tmpfs they are small.
      // A manifest that shares its number with an unrelated locked file on
      // another filesystem must not read as live.
      leftover(X)
      const manifest = publishMountPointManifest([X], [])!.file
      const inode = statSync(manifest).ino
      const elsewhere = withProcLocks(
        `1: POSIX  ADVISORY  WRITE 4242 fe:77:${inode} 0 EOF\n`,
      )
      try {
        expect(collectMountPoints()).toEqual([X])
      } finally {
        elsewhere.restore()
      }
      expect(existsSync(manifest)).toBe(false)
    },
  )

  it('is kept live by a lock on the manifest itself', () => {
    leftover(X)
    const manifest = publishMountPointManifest([X], [])!.file
    const inode = statSync(manifest).ino
    const onIt = withProcLocks(
      `1: POSIX  ADVISORY  READ 4242 ${deviceOf(manifest)}:${inode} 0 EOF\n`,
    )
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      onIt.restore()
    }
    expect(existsSync(manifest)).toBe(true)
    expect(existsSync(X)).toBe(true)
    // And goes with the lock.
    expect(collectMountPoints()).toEqual([X])
  })

  // ---- where the manifests are kept --------------------------------------

  const SHM = '/dev/shm'
  const SHM_WRITABLE = (() => {
    try {
      accessSync(SHM, constants.W_OK | constants.X_OK)
      return true
    } catch {
      return false
    }
  })()

  it.if(SHM_WRITABLE)(
    'are never kept under /dev, which the sandbox mounts afresh over them',
    () => {
      // bubblewrap opens the manifest after its mounts, and the wrap mounts a
      // new /dev after every bind: a manifest under /dev would not be there to
      // be opened.
      const shm = mkdtempSync(join(SHM, 'mount-point-manifests-'))
      chmodSync(shm, 0o700)
      try {
        // Whichever place is under /dev is passed over, the first as much as
        // the last.
        const elsewhere = TMP
        const underDev = { runtimeDir: shm, tempDir: shm }
        const fellBack = inAChild(PUBLISH, {
          env: { XDG_RUNTIME_DIR: shm, TMPDIR: elsewhere },
          places: underDev,
        })
        expect(fellBack.status).toBe(0)
        const manifest = JSON.parse(fellBack.stdout) as { file: string }
        expect(manifest.file.startsWith(`${elsewhere}/`)).toBe(true)
        expect(readdirSync(shm)).toEqual([])

        // With nowhere else to go it records nothing, rather than somewhere
        // bubblewrap cannot reach.
        const nowhere = inAChild(PUBLISH, {
          env: { XDG_RUNTIME_DIR: shm, TMPDIR: shm },
          places: underDev,
        })
        expect(nowhere.status).toBe(0)
        expect(JSON.parse(nowhere.stdout)).toBe(null)
        expect(readdirSync(shm)).toEqual([])
      } finally {
        rmSync(shm, { recursive: true, force: true })
      }
    },
    15000,
  )

  it("are not kept behind a link planted at the directory's name, whose target is left as it was", () => {
    // The name is predictable and sits where sandboxed commands commonly write.
    // A link there is refused, not followed.
    const target = join(BASE, 'somebody-elses')
    mkdirSync(target)
    chmodSync(target, 0o755)
    symlinkSync(target, join(TMP, `srt-mount-points-${process.getuid!()}`))
    const published = inAChild(PUBLISH, {
      places: { runtimeDir: join(BASE, 'no-runtime-directory') },
    })
    expect(published.status).toBe(0)
    expect(statSync(target).mode & 0o777).toBe(0o755)
    expect(readdirSync(target)).toEqual([])
    // Recorded all the same, in a directory of this process's own.
    const manifest = JSON.parse(published.stdout) as { file: string }
    expect(dirname(manifest.file)).toMatch(
      new RegExp(`^${TMP}/srt-mount-points-[A-Za-z0-9]{6}$`),
    )
  })

  it.if(BWRAP_CAN_NAMESPACE && NOT_ROOT)(
    'go to a directory this process can write when the usual one is read-only from here',
    () => {
      // A process inside a sandbox sees the directory bound read-only. It is
      // ours in every other respect, and must not be settled on.
      const elsewhere = TMP
      const published = inAChild(PUBLISH, {
        launcher: [
          'bwrap',
          '--dev-bind',
          '/',
          '/',
          '--ro-bind',
          DIR,
          DIR,
          '--',
        ],
      })
      expect(published.status).toBe(0)
      const manifest = JSON.parse(published.stdout) as { file: string } | null
      expect(manifest).not.toBe(null)
      expect(dirname(manifest!.file)).not.toBe(DIR)
      expect(manifest!.file.startsWith(`${elsewhere}/`)).toBe(true)
    },
    15000,
  )

  // ---- which directory is written to, and which are read ----
  //
  // Two processes of one user that differ in $XDG_RUNTIME_DIR or $TMPDIR must
  // still find each other's manifests. The user id and the file system say
  // where they go first, the same for every process, and what they name is read
  // by every process.

  /**
   * Four places of their own under `base`, none of them with a manifest
   * directory yet.
   */
  function fourPlaces(base = BASE): {
    places: { runtimeDir: string; tempDir: string }
    env: { XDG_RUNTIME_DIR: string; TMPDIR: string }
    /** The four manifest directories, in the order they are tried. */
    dirs: [string, string, string, string]
  } {
    const at = (name: string, mode: number): string => {
      const dir = join(base, name)
      mkdirSync(dir, { recursive: true })
      chmodSync(dir, mode)
      return dir
    }
    const places = {
      runtimeDir: at('run-user', 0o700),
      tempDir: at('tmp-root', 0o1777),
    }
    const env = {
      XDG_RUNTIME_DIR: at('xdg', 0o700),
      TMPDIR: at('tmpdir', 0o1777),
    }
    const perUser = `srt-mount-points-${process.getuid!()}`
    return {
      places,
      env,
      dirs: [
        join(places.runtimeDir, 'srt-mount-points'),
        join(places.tempDir, perUser),
        join(env.XDG_RUNTIME_DIR, 'srt-mount-points'),
        join(env.TMPDIR, perUser),
      ],
    }
  }

  /** A manifest directory as the library makes one. */
  function manifestDirectory(dir: string): string {
    mkdirSync(dir, { mode: 0o700 })
    chmodSync(dir, 0o700)
    return dir
  }

  /** What makes a manifest live for as long as this test runs: its writer. */
  function ofThisProcess(): Record<string, unknown> {
    return {
      pid: process.pid,
      start: readFileSync('/proc/self/stat', 'utf8')
        .split(') ')
        .pop()!
        .split(' ')[19],
    }
  }

  const LOOK = `console.log(JSON.stringify({ named: [...m.namedMountPoints().named].sort(), live: [...m.namedMountPoints().live].sort(), spared: [...m.liveMountPoints()].sort(), collected: m.collectMountPoints().sort() }))`
  type Looked = {
    named: string[]
    live: string[]
    spared: string[]
    collected: string[]
  }

  it('are written to the first directory that can be used: under the runtime directory, under /tmp, and only then where the environment says', () => {
    // Every combination of the four being usable or not. One that is not is
    // somebody's file at the name.
    for (let usable = 0; usable < 16; usable++) {
      const four = fourPlaces(join(BASE, `order-${usable}`))
      four.dirs.forEach((dir, index) => {
        if ((usable & (1 << index)) === 0) writeFileSync(dir, '')
      })
      const published = inAChild(PUBLISH, {
        env: four.env,
        places: four.places,
      })
      expect(published.status).toBe(0)
      const written = dirname(
        (JSON.parse(published.stdout) as { file: string }).file,
      )
      const first = four.dirs.find((_, index) => (usable & (1 << index)) !== 0)
      if (first !== undefined) {
        expect({ usable, written }).toEqual({ usable, written: first })
      } else {
        // A directory of the process's own, under its temp dir.
        expect(written).toMatch(
          new RegExp(`^${four.env.TMPDIR}/srt-mount-points-[A-Za-z0-9]{6}$`),
        )
      }
    }
  }, 60000)

  it('are one directory where two names lead to the same one', () => {
    // What the environment says is usually the runtime directory and /tmp
    // again, by those names or by others.
    const four = fourPlaces()
    const runtimeDir = join(BASE, 'runtime-by-another-name')
    const tempDir = join(BASE, 'tmp-by-another-name')
    symlinkSync(four.places.runtimeDir, runtimeDir)
    symlinkSync(four.places.tempDir, tempDir)
    const looked = inAChild(
      `console.log(JSON.stringify(m.mountPointManifestDirectories()))`,
      {
        env: { XDG_RUNTIME_DIR: runtimeDir, TMPDIR: tempDir },
        places: four.places,
      },
    )
    expect(looked.status).toBe(0)
    expect(JSON.parse(looked.stdout)).toEqual(four.dirs.slice(0, 2))
  })

  const notARuntimeDirectory: [string, (dir: string) => void][] = [
    ['is not there', dir => rmSync(dir, { recursive: true })],
    [
      'is a link to one',
      dir => {
        renameSync(dir, join(BASE, 'linked-to'))
        symlinkSync(join(BASE, 'linked-to'), dir)
      },
    ],
    ['can be looked into by the group', dir => chmodSync(dir, 0o750)],
    ['can be looked into by others', dir => chmodSync(dir, 0o705)],
  ]
  for (const [what, spoil] of notARuntimeDirectory) {
    it(`are neither written nor read, nor is anything made, under a runtime directory that ${what}`, () => {
      const four = fourPlaces()
      // What is there for this user to find, with a manifest in it that would
      // keep X.
      const planted = join(four.places.runtimeDir, 'srt-mount-points')
      manifestDirectory(planted)
      leftover(X)
      manifestOfADeadProcess([X], ofThisProcess(), planted)
      spoil(four.places.runtimeDir)
      const before = existsSync(planted) ? readdirSync(planted) : undefined

      const published = inAChild(PUBLISH, {
        env: { TMPDIR: four.env.TMPDIR },
        places: four.places,
      })
      expect(published.status).toBe(0)
      expect(
        dirname((JSON.parse(published.stdout) as { file: string }).file),
      ).toBe(four.dirs[1])
      const looked = inAChild(
        [
          `const directories = m.mountPointManifestDirectories()`,
          `const named = [...m.namedMountPoints().named]`,
          `console.log(JSON.stringify({ directories, named: named.filter(p => p === ${JSON.stringify(X)}), spared: [...m.liveMountPoints()] }))`,
        ].join('\n'),
        { env: { TMPDIR: four.env.TMPDIR }, places: four.places },
      )
      expect(looked.status).toBe(0)
      expect(JSON.parse(looked.stdout)).toEqual({
        directories: [four.dirs[1], four.dirs[3]],
        named: [],
        spared: [],
      })
      expect(existsSync(planted) ? readdirSync(planted) : undefined).toEqual(
        before,
      )
    }, 15000)
  }

  /**
   * Has `dir` look like another user's to whoever asks: nothing here can make
   * a directory that is.
   */
  function asSomebodyElses(dir: string): { restore(): void } {
    const lstat = fs.lstatSync
    const spy = spyOn(fs, 'lstatSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      const stat = (lstat as (f: unknown, o: unknown) => fs.Stats)(
        file,
        options,
      )
      if (file !== dir) return stat
      const other = Object.create(
        Object.getPrototypeOf(stat) as object,
      ) as fs.Stats
      return Object.assign(other, stat, { uid: stat.uid + 1 })
    }) as never)
    return { restore: () => spy.mockRestore() }
  }

  it("are neither written nor read under a runtime directory that is somebody else's", () => {
    const four = fourPlaces()
    const planted = manifestDirectory(
      join(four.places.runtimeDir, 'srt-mount-points'),
    )
    leftover(X)
    manifestOfADeadProcess([X], ofThisProcess(), planted)
    const theirs = asSomebodyElses(four.places.runtimeDir)
    setMountPointManifestPlacesForTesting({
      ...four.places,
      environmentRuntimeDir: undefined,
      environmentTempDir: four.env.TMPDIR,
    })
    try {
      expect(mountPointManifestDirectories()).toEqual([
        four.dirs[1],
        four.dirs[3],
      ])
      expect(
        dirname(publishMountPointManifest([join(BASE, 'absent')], [])!.file),
      ).toBe(four.dirs[1])
      expect([...namedMountPoints().named]).toEqual([join(BASE, 'absent')])
      expect([...liveMountPoints()]).toEqual([])
      expect(readdirSync(planted).length).toBe(1)
    } finally {
      theirs.restore()
      collectMountPoints()
      setMountPointManifestPlacesForTesting(runtime.places())
    }
  })

  for (const differing of ['XDG_RUNTIME_DIR', 'TMPDIR'] as const) {
    it(`are read by a process whose ${differing} is not the writer's`, async () => {
      // A login shell and what a service or an IDE starts, two shells with a
      // temp dir each: the second has to find what the first wrote.
      const four = fourPlaces()
      const environment = (n: number): Record<string, string | undefined> => {
        const own = join(BASE, `${differing.toLowerCase()}-${n}`)
        mkdirSync(own, { recursive: true })
        chmodSync(own, 0o700)
        return differing === 'XDG_RUNTIME_DIR'
          ? { XDG_RUNTIME_DIR: own, TMPDIR: four.env.TMPDIR }
          : { XDG_RUNTIME_DIR: undefined, TMPDIR: own }
      }
      leftover(X)
      const go = join(BASE, 'go')
      const up = join(BASE, 'up')
      // The first process wraps, and its sandbox runs for as long as it is
      // not told to go: its manifest is live for being its own.
      const writer = spawn(
        process.execPath,
        [
          writeChild(
            'writer.ts',
            [
              `import { existsSync, writeFileSync } from 'node:fs'`,
              `m.publishMountPointManifest([${JSON.stringify(X)}], [])`,
              `writeFileSync(${JSON.stringify(up)}, '')`,
              `while (!existsSync(${JSON.stringify(go)})) await new Promise(resolve => setTimeout(resolve, 20))`,
            ].join('\n'),
            four.places,
          ),
        ],
        { env: childEnv(environment(1)), stdio: 'ignore' },
      )
      const writerExited = new Promise(resolve => writer.on('exit', resolve))
      try {
        const deadline = Date.now() + 10000
        while (!existsSync(up)) {
          if (Date.now() > deadline) throw new Error('the writer never wrote')
          await new Promise(resolve => setTimeout(resolve, 20))
        }
        const second = inAChild(LOOK, {
          env: environment(2),
          places: four.places,
        })
        expect(second.status).toBe(0)
        expect(JSON.parse(second.stdout) as Looked).toEqual({
          named: [X],
          live: [X],
          spared: [X],
          collected: [],
        })
        expect(existsSync(X)).toBe(true)
      } finally {
        writeFileSync(go, '')
        await writerExited
      }

      // And once the first is gone, and past its grace, the second is the one
      // that takes away what it left.
      await new Promise(resolve => setTimeout(resolve, 600))
      const after = inAChild(LOOK, {
        env: environment(2),
        places: four.places,
      })
      expect(JSON.parse(after.stdout) as Looked).toEqual({
        named: [X],
        live: [],
        spared: [],
        collected: [X],
      })
      expect(existsSync(X)).toBe(false)
      for (const dir of four.dirs) {
        if (existsSync(dir)) {
          expect(readdirSync(dir).filter(n => n.endsWith('.json'))).toEqual([])
        }
      }
    }, 30000)
  }

  it('are believed in a directory this process does not write to', () => {
    // This process writes under the runtime directory. What a process
    // without one wrote under /tmp counts all the same: for a wrap that finds
    // something at a path, and for a clean-up that is about to remove it.
    const theirs = manifestDirectory(THEIRS)
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const mine = manifestOfADeadProcess([X, Y])
    const live = manifestOfADeadProcess([X], ofThisProcess(), theirs)
    const finished = manifestOfADeadProcess([Y], {}, theirs)

    const named = namedMountPoints()
    expect([...named.named].sort()).toEqual([X, Y].sort())
    expect([...named.live]).toEqual([X])
    expect([...liveMountPoints()]).toEqual([X])

    // What only finished manifests name goes, and they go with it, wherever
    // they are; what a live one names stays, wherever that one is.
    expect(collectMountPoints()).toEqual([Y])
    expect(existsSync(X)).toBe(true)
    expect(existsSync(live)).toBe(true)
    expect(existsSync(finished)).toBe(false)
    expect(existsSync(mine)).toBe(false)
    expect(readdirSync(theirs)).toEqual([basename(live)])

    rmSync(live)
    manifestOfADeadProcess([X], {}, theirs)
    expect(collectMountPoints()).toEqual([X])
    expect(readdirSync(theirs)).toEqual([])
    // And all the while this process wrote under the runtime directory.
    expect(
      dirname(publishMountPointManifest([join(BASE, 'absent')], [])!.file),
    ).toBe(DIR)
  })

  it('keeps a mount point named by a manifest that is published in another directory while the pass is under way', () => {
    const theirs = manifestDirectory(THEIRS)
    leftover(X)
    manifestOfADeadProcess([X])
    let arrived: string | undefined
    const pass = duringTheNextPass(() => {
      arrived = manifestOfADeadProcess([X], { created: Date.now() }, theirs)
    })
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      pass.restore()
    }
    expect(arrived).toBeDefined()
    expect(existsSync(X)).toBe(true)
  })

  it('keeps what a finished manifest names when the lock on a manifest in another directory shows on the look before the removals', () => {
    const theirs = manifestDirectory(THEIRS)
    leftover(X)
    manifestOfADeadProcess([X])
    const locked = manifestOfADeadProcess([X], {}, theirs)
    const line = `1: POSIX  ADVISORY  READ 4242 ${deviceOf(locked)}:${statSync(locked).ino} 0 EOF\n`
    const readFile = fs.readFileSync
    let reads = 0
    const spy = spyOn(fs, 'readFileSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      if (file === '/proc/locks') {
        reads++
        return reads === 1 ? '' : line
      }
      return (readFile as (f: unknown, o: unknown) => unknown)(file, options)
    }) as never)
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(X)).toBe(true)
    expect(existsSync(locked)).toBe(true)
  })

  const notOurs: [string, (dir: string) => { restore(): void } | void][] = [
    [
      'is a link to a directory',
      dir => {
        const target = join(BASE, 'linked-to')
        renameSync(dir, target)
        symlinkSync(target, dir)
      },
    ],
    ['can be written by others', dir => chmodSync(dir, 0o777)],
    ['can be looked into by the group', dir => chmodSync(dir, 0o750)],
    ["is somebody else's", asSomebodyElses],
  ]
  for (const [what, spoil] of notOurs) {
    it(`are not believed in a directory that ${what}, which is left as it is`, () => {
      const theirs = manifestDirectory(THEIRS)
      const Y = join(BASE, 'second.lock')
      const Z = join(BASE, 'third.lock')
      leftover(X)
      leftover(Y)
      leftover(Z)
      // One that would keep X, and one that would have Y removed.
      manifestOfADeadProcess([X], ofThisProcess(), theirs)
      manifestOfADeadProcess([Y], {}, theirs)
      manifestOfADeadProcess([X, Z])
      const spoilt = spoil(theirs)
      try {
        const before = readdirSync(theirs).sort()
        const mode = statSync(theirs).mode & 0o777

        const named = namedMountPoints()
        expect([...named.named].sort()).toEqual([X, Z].sort())
        expect([...named.live]).toEqual([])
        expect([...liveMountPoints()]).toEqual([])
        expect(collectMountPoints().sort()).toEqual([X, Z].sort())
        expect(existsSync(Y)).toBe(true)

        expect(readdirSync(theirs).sort()).toEqual(before)
        expect(statSync(theirs).mode & 0o777).toBe(mode)
      } finally {
        spoilt?.restore()
      }
    })
  }

  it('are read in both directories that come from the user id, in none the environment names beside them, and none is made for it', () => {
    const four = fourPlaces()
    const paths = four.dirs.map((dir, index) => {
      const held = join(BASE, `held-${index}.lock`)
      leftover(held)
      // The last is not there, and is not made.
      if (index < 3) {
        manifestOfADeadProcess([held], ofThisProcess(), manifestDirectory(dir))
      }
      return held
    })
    const looked = inAChild(
      `console.log(JSON.stringify([...m.liveMountPoints()].sort()))`,
      { env: four.env, places: four.places },
    )
    expect(looked.status).toBe(0)
    expect(JSON.parse(looked.stdout)).toEqual(paths.slice(0, 2).sort())
    expect(existsSync(four.dirs[3])).toBe(false)
    for (const dir of four.dirs.slice(0, 3)) {
      expect(readdirSync(dir).length).toBe(1)
    }
  })

  // What the environment names is kept out of a sandboxed command's reach only
  // by processes whose environment names it. So a manifest found there is
  // believed only by a process that has nowhere else to keep its own.

  /**
   * In each directory the environment names: the manifest of a running sandbox,
   * which would keep X, and one a dead process left, which would have Y
   * removed.
   */
  function whereTheEnvironmentSays(
    four: ReturnType<typeof fourPlaces>,
    Y: string,
  ): string[] {
    return four.dirs.slice(2).flatMap(dir => {
      manifestDirectory(dir)
      return [
        manifestOfADeadProcess([X], ofThisProcess(), dir),
        manifestOfADeadProcess([Y], {}, dir),
      ]
    })
  }

  for (const usable of ['the runtime directory', '/tmp'] as const) {
    it(`are not believed where the environment says, by a process that can use the directory under ${usable}`, () => {
      const four = fourPlaces()
      if (usable === '/tmp') rmSync(four.places.runtimeDir, { recursive: true })
      const Y = join(BASE, 'second.lock')
      leftover(X)
      leftover(Y)
      const planted = whereTheEnvironmentSays(four, Y)
      // What a process of the user left, where every process looks.
      const finished = manifestOfADeadProcess(
        [X],
        {},
        manifestDirectory(four.dirs[1]),
      )

      const published = inAChild(PUBLISH, {
        env: four.env,
        places: four.places,
      })
      expect(
        dirname((JSON.parse(published.stdout) as { file: string }).file),
      ).toBe(usable === '/tmp' ? four.dirs[1] : four.dirs[0])
      rmSync((JSON.parse(published.stdout) as { file: string }).file)

      const looked = inAChild(LOOK, { env: four.env, places: four.places })
      expect(looked.status).toBe(0)
      // X is kept by nothing that is believed, and goes on the word of the
      // one manifest that is; Y is named by nothing that is believed, and
      // stays.
      expect(JSON.parse(looked.stdout) as Looked).toEqual({
        named: [X],
        live: [],
        spared: [],
        collected: [X],
      })
      expect(existsSync(X)).toBe(false)
      expect(existsSync(Y)).toBe(true)
      expect(existsSync(finished)).toBe(false)
      for (const manifest of planted) {
        expect(existsSync(manifest)).toBe(true)
      }
    }, 15000)
  }

  it('are believed where the environment says, and collected there, by a process that can use no directory that comes from the user id', () => {
    const four = fourPlaces()
    rmSync(four.places.runtimeDir, { recursive: true })
    writeFileSync(four.dirs[1], '')
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const planted = whereTheEnvironmentSays(four, Y)

    const looked = inAChild(LOOK, { env: four.env, places: four.places })
    expect(looked.status).toBe(0)
    expect(JSON.parse(looked.stdout) as Looked).toEqual({
      named: [X, Y].sort(),
      live: [X],
      spared: [X],
      collected: [Y],
    })
    expect(existsSync(X)).toBe(true)
    expect(existsSync(Y)).toBe(false)
    // The ones that named X for a running sandbox stay, in both; the ones a
    // dead process left are gone, from both.
    expect(planted.map(manifest => existsSync(manifest))).toEqual([
      true,
      false,
      true,
      false,
    ])

    // And it is where this process writes: to the first of the two.
    const published = inAChild(PUBLISH, {
      env: four.env,
      places: four.places,
    })
    expect(
      dirname((JSON.parse(published.stdout) as { file: string }).file),
    ).toBe(four.dirs[2])
  }, 15000)

  it('are believed and collected in the directory a process settled on where the environment says, after one that comes from the user id has become usable', () => {
    // Nothing that comes from the user id will do when the process first
    // records, so it settles where its environment says, and stays there:
    // its manifests are there, and the sandboxes that hold their locks.
    const four = fourPlaces()
    rmSync(four.places.runtimeDir, { recursive: true })
    writeFileSync(four.dirs[1], '')
    const [settled, other] = [four.dirs[2], four.dirs[3]]
    const Y = join(BASE, 'second.lock')
    const Z = join(BASE, 'third.lock')
    leftover(X)
    leftover(Y)
    leftover(Z)
    manifestOfADeadProcess([Y], {}, manifestDirectory(settled))
    const notBelieved = manifestOfADeadProcess(
      [Z],
      {},
      manifestDirectory(other),
    )

    const ran = inAChild(
      [
        `import { rmSync } from 'node:fs'`,
        `import { dirname } from 'node:path'`,
        `const first = m.publishMountPointManifest([${JSON.stringify(X)}], [])`,
        // Somebody's file at the name under /tmp goes, and the next wrap
        // makes the directory.
        `rmSync(${JSON.stringify(four.dirs[1])})`,
        `const directories = m.mountPointManifestDirectories()`,
        `const named = m.namedMountPoints()`,
        `const second = m.publishMountPointManifest([${JSON.stringify(join(BASE, 'absent'))}], [])`,
        `const collected = m.collectMountPoints().sort()`,
        `console.log(JSON.stringify({ first: dirname(first.file), second: dirname(second.file), directories, named: [...named.named].sort(), live: [...named.live], collected }))`,
      ].join('\n'),
      { env: four.env, places: four.places },
    )
    expect(ran.status).toBe(0)
    expect(JSON.parse(ran.stdout)).toEqual({
      first: settled,
      second: settled,
      directories: [four.dirs[1], settled, other],
      named: [X, Y].sort(),
      live: [X],
      collected: [X, Y].sort(),
    })
    expect(existsSync(X)).toBe(false)
    expect(existsSync(Y)).toBe(false)
    expect(readdirSync(settled).filter(n => n.endsWith('.json'))).toEqual([])
    // What the environment names beside it is nobody's word any more.
    expect(existsSync(Z)).toBe(true)
    expect(existsSync(notBelieved)).toBe(true)
  }, 15000)

  // ---- what is read as a manifest ----
  //
  // Only a regular file of the user's, of a size a manifest can have, is read:
  // a link is not followed and a FIFO is not opened.

  /** Thirty seconds old: nothing can be starting under it any more. */
  function aged(file: string): string {
    const halfAMinuteAgo = new Date(Date.now() - 30_000)
    utimesSync(file, halfAMinuteAgo, halfAMinuteAgo)
    return file
  }

  /** What a manifest of a dead process naming `paths` holds. */
  function finishedManifestText(paths: string[]): string {
    const file = manifestOfADeadProcess(paths)
    const text = readFileSync(file, 'utf8')
    rmSync(file)
    return text
  }

  const notAManifest: [string, (name: string, paths: string[]) => void][] = [
    [
      'a link to a manifest kept somewhere else',
      (name, paths) => {
        const elsewhere = join(BASE, 'elsewhere.json')
        writeFileSync(elsewhere, finishedManifestText(paths), { mode: 0o600 })
        aged(elsewhere)
        symlinkSync(elsewhere, name)
      },
    ],
    [
      'a manifest of more than a mebibyte',
      (name, paths) => {
        writeFileSync(
          name,
          finishedManifestText(paths) + ' '.repeat(1024 * 1024),
          { mode: 0o600 },
        )
        aged(name)
      },
    ],
    [
      'a directory',
      name => {
        mkdirSync(name)
        aged(name)
      },
    ],
  ]
  for (const [what, plant] of notAManifest) {
    it(`passes over ${what}, and what it names`, () => {
      const Y = join(BASE, 'second.lock')
      leftover(X)
      leftover(Y)
      plant(join(DIR, '4242-0123456789abcdef.json'), [X])
      manifestOfADeadProcess([Y])

      expect([...namedMountPoints().named]).toEqual([Y])
      // Nor does it stand in the way of the manifests beside it.
      expect(collectMountPoints()).toEqual([Y])
      expect(existsSync(X)).toBe(true)
    })
  }

  it("passes over a manifest that is somebody else's", () => {
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const theirs = aged(manifestOfADeadProcess([X]))
    const inode = statSync(theirs, { bigint: true }).ino
    manifestOfADeadProcess([Y])
    // As another user's would look: nothing here can make one.
    const fstat = fs.fstatSync
    const spy = spyOn(fs, 'fstatSync').mockImplementation(((
      fd: unknown,
      options: unknown,
    ) => {
      const stat = (fstat as (f: unknown, o: unknown) => fs.BigIntStats)(
        fd,
        options,
      )
      if (stat.ino !== inode) return stat
      const other = Object.create(
        Object.getPrototypeOf(stat) as object,
      ) as fs.BigIntStats
      return Object.assign(other, stat, { uid: stat.uid + 1n })
    }) as never)
    try {
      expect([...namedMountPoints().named]).toEqual([Y])
      expect(collectMountPoints()).toEqual([Y])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(X)).toBe(true)
  })

  it('passes over a FIFO nobody writes to, and is not held up by it', () => {
    const Y = join(BASE, 'second.lock')
    leftover(Y)
    manifestOfADeadProcess([Y])
    const fifo = join(DIR, '4242-0123456789abcdef.json')
    expect(spawnSync('mkfifo', [fifo]).status).toBe(0)
    aged(fifo)
    // In a process of its own: opening a FIFO to read waits for a writer, on
    // the one thread there is.
    const looked = inAChild(
      `console.log(JSON.stringify({ named: [...m.namedMountPoints().named], live: [...m.liveMountPoints()], collected: m.collectMountPoints() }))`,
    )
    expect(looked.status).toBe(0)
    expect(looked.ms).toBeLessThan(AT_ONCE_MS)
    expect(JSON.parse(looked.stdout)).toEqual({
      named: [Y],
      live: [],
      collected: [Y],
    })
  }, 15000)

  // ---- which mount points a running sandbox relies on ----
  //
  // A caller that removes paths itself after a command can ask first which to
  // leave out. What it is told to leave out is never more than an empty
  // placeholder.

  /** The set, as a sorted list. */
  function live(): string[] {
    return [...liveMountPoints()].sort()
  }

  /** Has /proc/locks refuse to be read. */
  function withUnreadableProcLocks(): { restore(): void } {
    const readFile = fs.readFileSync
    const spy = spyOn(fs, 'readFileSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      if (file === '/proc/locks') {
        throw Object.assign(new Error('EACCES: /proc/locks'), {
          code: 'EACCES',
        })
      }
      return (readFile as (f: unknown, o: unknown) => unknown)(file, options)
    }) as never)
    return { restore: () => spy.mockRestore() }
  }

  it('holds a mount point while a live manifest names it, file or directory, and no other path', () => {
    const directory = join(BASE, 'empty-directory')
    const other = join(BASE, 'other.lock')
    leftover(X)
    mkdirSync(directory)
    leftover(other)
    // Of this process, and not released: live.
    const manifest = publishMountPointManifest(
      [X, directory, join(BASE, 'never-there')],
      [],
    )!.file

    expect(live()).toEqual([X, directory].sort())
    // Asking takes nothing away.
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)

    expect(collectMountPoints().sort()).toEqual([X, directory].sort())
    expect(live()).toEqual([])
  })

  it('no longer holds a path once something has been written to it, though a live manifest still names it', () => {
    leftover(X)
    publishMountPointManifest([X], [])
    expect(live()).toEqual([X])

    chmodSync(X, 0o644)
    writeFileSync(X, 'x')
    chmodSync(X, 0o444)
    expect(live()).toEqual([])
  })

  it('holds nothing a live manifest names that does not look like a mount point any more', () => {
    const writable = join(BASE, 'writable')
    writeFileSync(writable, '')
    chmodSync(writable, 0o644)
    const linked = join(BASE, 'linked')
    leftover(linked)
    linkSync(linked, join(BASE, 'linked-again'))
    const pointer = join(BASE, 'pointer')
    leftover(join(BASE, 'pointed-at'))
    symlinkSync(join(BASE, 'pointed-at'), pointer)
    const inUse = join(BASE, 'directory-in-use')
    mkdirSync(inUse)
    writeFileSync(join(inUse, 'file'), '')
    const theirs = join(BASE, 'somebody-elses')
    leftover(theirs)
    const theirDirectory = join(BASE, 'somebody-elses-directory')
    mkdirSync(theirDirectory)
    leftover(X)
    publishMountPointManifest(
      [writable, linked, pointer, inUse, theirs, theirDirectory, X],
      [],
    )
    // As another user's would look: nothing here can make one.
    const lstat = fs.lstatSync
    const spy = spyOn(fs, 'lstatSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      const stat = (lstat as (f: unknown, o: unknown) => fs.Stats)(
        file,
        options,
      )
      if (file === theirs || file === theirDirectory) {
        const other = Object.create(
          Object.getPrototypeOf(stat) as object,
        ) as fs.Stats
        return Object.assign(other, stat, { uid: stat.uid + 1 })
      }
      return stat
    }) as never)
    try {
      expect(live()).toEqual([X])
    } finally {
      spy.mockRestore()
    }
  })

  it('holds what a finished manifest names only when a sandbox holds the lock on it', () => {
    leftover(X)
    const manifest = manifestOfADeadProcess([X])
    expect(live()).toEqual([])

    const onIt = withProcLocks(
      `1: POSIX  ADVISORY  READ 4242 ${deviceOf(manifest)}:${statSync(manifest).ino} 0 EOF\n`,
    )
    try {
      expect(live()).toEqual([X])
    } finally {
      onIt.restore()
    }
  })

  it('holds what any manifest names where /proc/locks cannot be read, and of that only what looks like a mount point', () => {
    const written = join(BASE, 'written-to')
    writeFileSync(written, 'mine')
    chmodSync(written, 0o444)
    leftover(X)
    leftover(join(BASE, 'other.lock'))
    manifestOfADeadProcess([X, written])
    const unreadable = withUnreadableProcLocks()
    try {
      expect(live()).toEqual([X])
    } finally {
      unreadable.restore()
    }
  })

  it('holds what any manifest names while a manifest that cannot be read may have a sandbox under it', () => {
    // What another version of this library wrote, say. What it names cannot be
    // listed, so while the clean-up takes it to be live every named path
    // counts.
    const written = join(BASE, 'written-to')
    writeFileSync(written, 'mine')
    chmodSync(written, 0o444)
    leftover(X)
    manifestOfADeadProcess([X, written])
    const stranger = join(DIR, '1-garbage.json')
    writeFileSync(stranger, '{ not json')
    expect(live()).toEqual([X])

    aged(stranger)
    expect(live()).toEqual([])

    const onIt = withProcLocks(
      `1: POSIX  ADVISORY  READ 4242 ${deviceOf(stranger)}:${statSync(stranger).ino} 0 EOF\n`,
    )
    try {
      expect(live()).toEqual([X])
    } finally {
      onIt.restore()
    }
  })

  it('is one listing of the directory and one reading of /proc/locks, under no lock', () => {
    leftover(X)
    publishMountPointManifest([X], [])
    manifestOfADeadProcess([join(BASE, 'other.lock')])
    // Somebody holds the directory's lock: this process, which is running.
    const start = readFileSync('/proc/self/stat', 'utf8')
      .split(') ')
      .pop()!
      .split(' ')[19]
    const held = `${process.pid} ${start} ${OWN_NAMESPACE}\n`
    writeFileSync(LOCK, held)
    const before = readdirSync(DIR).sort()

    const readFile = spyOn(fs, 'readFileSync')
    const readdir = spyOn(fs, 'readdirSync')
    let listed: string[]
    let looks: number
    let listings: number
    let tookMs: number
    try {
      const began = Date.now()
      listed = live()
      tookMs = Date.now() - began
      looks = readFile.mock.calls.filter(
        ([file]) => file === '/proc/locks',
      ).length
      listings = readdir.mock.calls.filter(([dir]) => dir === DIR).length
    } finally {
      readFile.mockRestore()
      readdir.mockRestore()
    }
    expect(listed).toEqual([X])
    expect(looks).toBe(1)
    expect(listings).toBe(1)
    // Not waited for, not taken, not broken.
    expect(tookMs).toBeLessThan(1000)
    expect(readFileSync(LOCK, 'utf8')).toBe(held)
    expect(readdirSync(DIR).sort()).toEqual(before)
  })

  /** A runtime directory with nothing in it yet. */
  function emptyRuntimeDirectory(name: string): string {
    const dir = join(BASE, name)
    mkdirSync(dir, { mode: 0o700 })
    chmodSync(dir, 0o700)
    return dir
  }

  it('makes no manifest directory where there is none, and holds nothing then', () => {
    const run = emptyRuntimeDirectory('run')
    const xdg = emptyRuntimeDirectory('xdg')
    const tmp = join(BASE, 'tmp-root')
    mkdirSync(tmp)
    const looked = inAChild(
      `console.log(JSON.stringify([...m.liveMountPoints()]))`,
      {
        env: { XDG_RUNTIME_DIR: xdg },
        places: { runtimeDir: run, tempDir: tmp },
      },
    )
    expect(looked.status).toBe(0)
    expect(JSON.parse(looked.stdout)).toEqual([])
    for (const place of [run, xdg, tmp, TMP]) {
      expect(readdirSync(place)).toEqual([])
    }
  })

  it('reads the directory under the temp dir, where that is the one there is', () => {
    const theirs = join(TMP, `srt-mount-points-${process.getuid!()}`)
    mkdirSync(theirs, { mode: 0o700 })
    chmodSync(theirs, 0o700)
    leftover(X)
    const manifest = manifestOfADeadProcess([X], {
      pid: process.pid,
      start: readFileSync('/proc/self/stat', 'utf8')
        .split(') ')
        .pop()!
        .split(' ')[19],
    })
    writeFileSync(
      join(theirs, '4242-0123456789abcdef.json'),
      readFileSync(manifest, 'utf8'),
      { mode: 0o600 },
    )
    rmSync(manifest)
    const run = emptyRuntimeDirectory('run')
    const looked = inAChild(
      `console.log(JSON.stringify([...m.liveMountPoints()]))`,
      { places: { runtimeDir: run } },
    )
    expect(looked.status).toBe(0)
    expect(JSON.parse(looked.stdout)).toEqual([X])
    expect(readdirSync(run)).toEqual([])
  })

  it('holds nothing, and makes nothing, where the platform is not Linux', () => {
    leftover(X)
    publishMountPointManifest([X], [])
    const before = readdirSync(DIR).sort()
    const elsewhere = inAChild(
      `console.log(JSON.stringify([...m.liveMountPoints()]))`,
      {
        first: `Object.defineProperty(process, 'platform', { value: 'darwin' })`,
      },
    )
    expect(elsewhere.status).toBe(0)
    expect(JSON.parse(elsewhere.stdout)).toEqual([])
    expect(readdirSync(DIR).sort()).toEqual(before)
    expect(readdirSync(TMP)).toEqual([])
  })

  // ---- all of it is bubblewrap's, which is Linux's -----------------------

  it('does nothing at all where the platform is not Linux', () => {
    // Every clean-up after a command, on every platform, comes through here.
    // Off Linux it must make nothing.
    leftover(X)
    manifestOfADeadProcess([X])
    const before = readdirSync(DIR).sort()
    const elsewhere = inAChild(
      [
        `const u = await import(${LIBRARY})`,
        `const published = m.publishMountPointManifest([${JSON.stringify(X)}], []) ?? null`,
        `const live = [...m.liveMountPoints()]`,
        `const directories = m.mountPointManifestDirectories()`,
        `const collected = m.collectMountPoints()`,
        `u.cleanupBwrapMountPoints()`,
        `u.cleanupBwrapMountPoints({ force: true })`,
        `console.log(JSON.stringify({ published, live, directories, collected }))`,
      ].join('\n'),
      {
        first: `Object.defineProperty(process, 'platform', { value: 'darwin' })`,
      },
    )
    expect(elsewhere.status).toBe(0)
    expect(JSON.parse(elsewhere.stdout)).toEqual({
      published: null,
      live: [],
      directories: [],
      collected: [],
    })
    expect(existsSync(X)).toBe(true)
    expect(readdirSync(DIR).sort()).toEqual(before)
    expect(readdirSync(TMP)).toEqual([])
  })
})
