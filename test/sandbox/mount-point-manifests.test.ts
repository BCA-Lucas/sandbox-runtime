import { describe, it, expect, beforeEach, afterEach, spyOn } from 'bun:test'
import { spawnSync } from 'node:child_process'
import * as fs from 'node:fs'
import {
  chmodSync,
  existsSync,
  linkSync,
  lstatSync,
  lutimesSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  readdirSync,
  readlinkSync,
  realpathSync,
  rmSync,
  statSync,
  symlinkSync,
  utimesSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { basename, dirname, join } from 'node:path'
import {
  collectMountPoints,
  forgetMountPointManifestDirectory,
  liveMountPoints,
  namedMountPoints,
  publishMountPointManifest,
} from '../../src/sandbox/bwrap-mount-manifests.js'
import { bwrapCanNamespace } from '../helpers/bwrap-namespace.js'
import { isLinux } from '../helpers/platform.js'
import { usePrivateManifestDirectory } from '../helpers/private-manifest-directory.js'

/**
 * The manifests and the pass that collects on their word, below the level of a
 * sandbox: which process a pass asks after, what it claims and looks at again
 * before it removes anything, and that what it cannot tell it leaves.
 */
describe.if(isLinux)('The mount point manifests', () => {
  const runtime = usePrivateManifestDirectory()
  const MODULE = JSON.stringify(
    join(import.meta.dir, '../../src/sandbox/bwrap-mount-manifests.ts'),
  )
  const LIBRARY = JSON.stringify(
    join(import.meta.dir, '../../src/sandbox/linux-sandbox-utils.ts'),
  )
  const BWRAP_CAN_NAMESPACE = bwrapCanNamespace()
  const NOT_ROOT = process.getuid?.() !== 0
  const OWN_NAMESPACE = isLinux ? readlinkSync('/proc/self/ns/pid') : ''

  let BASE: string
  let DIR: string // where the manifests go
  let X: string // a mount point an earlier sandbox left
  let TMP: string // the temp dir of every child process

  beforeEach(() => {
    BASE = realpathSync(mkdtempSync(join(tmpdir(), 'mount-point-manifests-')))
    TMP = join(BASE, 'tmp')
    mkdirSync(TMP)
    DIR = runtime.manifestDir()
    mkdirSync(DIR, { recursive: true, mode: 0o700 })
    chmodSync(DIR, 0o700)
    X = join(BASE, 'config.lock')
  })

  afterEach(() => {
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
  ): string {
    const pid = deadPid()
    const file = join(DIR, `${pid}-${Math.random().toString(16).slice(2)}.json`)
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

  /** Field 22 of a /proc/PID/stat line: when that process started. */
  function startOf(stat: string): string {
    return stat
      .slice(stat.lastIndexOf(')') + 1)
      .trim()
      .split(' ')[19]!
  }

  /** This process, which is running, as a manifest or a record names one. */
  function thisProcess(): { pid: number; start: string } {
    return {
      pid: process.pid,
      start: startOf(readFileSync('/proc/self/stat', 'utf8')),
    }
  }

  /**
   * The line the wrapper shell records for a process, with a name that holds
   * what a careless reading would trip over.
   */
  function statLine(who: { pid: number; start: string }): string {
    const after = ['S', ...Array<string>(18).fill('0'), who.start, '0', '0']
    return `${who.pid} (a) b (c) ${after.join(' ')}\n`
  }

  /** Where the started record of `manifest` is. */
  function recordOf(manifest: string): string {
    return manifest.replace(/\.json$/, '.started')
  }

  /** Puts `manifest` on record as started by those processes, in that order. */
  function started(
    manifest: string,
    ...by: { pid: number; start: string }[]
  ): string {
    writeFileSync(recordOf(manifest), by.map(statLine).join(''), {
      mode: 0o600,
    })
    return manifest
  }

  /** The claims in the manifest directory, by name. */
  function claims(): string[] {
    return readdirSync(DIR).filter(name => name.endsWith('.claimed'))
  }

  /** The name a pass gives `manifest` when it claims it. */
  function claimOf(manifest: string): string {
    return basename(manifest).replace(/\.json$/, '.claimed')
  }

  /**
   * Runs `source` with the module as `m` in a process of its own, which is
   * killed if it does not end by itself: what these cases guard against blocks
   * the thread. `first` runs before the module is loaded, and an `env` entry
   * that is undefined is removed from the child's environment.
   */
  function inAChild(
    source: string,
    options: {
      launcher?: string[]
      env?: Record<string, string | undefined>
      first?: string
    } = {},
  ): { status: number | null; ms: number; stdout: string } {
    const script = join(BASE, `child-${Math.random().toString(16).slice(2)}.ts`)
    writeFileSync(
      script,
      `${options.first ?? ''}\nconst m = await import(${MODULE})\n${source}\n`,
    )
    const argv = [...(options.launcher ?? []), process.execPath, script]
    // A temp dir of its own: it is where the manifests go when the runtime
    // directory will not do, and the real one is every other process's.
    const env: Record<string, string | undefined> = {
      ...process.env,
      TMPDIR: TMP,
      ...options.env,
    }
    for (const [name, value] of Object.entries(env)) {
      if (value === undefined) delete env[name]
    }
    const began = Date.now()
    const run = spawnSync(argv[0]!, argv.slice(1), {
      env: env as Record<string, string>,
      encoding: 'utf8',
      timeout: 6000,
      killSignal: 'SIGKILL',
    })
    return { status: run.status, ms: Date.now() - began, stdout: run.stdout }
  }

  const COLLECT = `m.collectMountPoints()`
  // Well under the time a read that blocks would hold a child up for.
  const AT_ONCE_MS = 1500
  const PUBLISH = `console.log(JSON.stringify(m.publishMountPointManifest(['/nonexistent/x'], []) ?? null))`

  it.if(BWRAP_CAN_NAMESPACE && NOT_ROOT)(
    'collects nothing on the word of a directory that is read-only from here',
    () => {
      // What a process inside a sandbox sees of the directory. It keeps its own
      // manifests elsewhere and does not judge what is in this one.
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
      expect(existsSync(X)).toBe(true)
      expect(existsSync(manifest)).toBe(true)
    },
    15000,
  )

  // ---- what a pass removes -----------------------------------------------

  /**
   * Runs `during` once, in the middle of the next pass: when it has claimed
   * the first finished manifest, before it reads that manifest's record again
   * and before it removes anything.
   */
  function duringTheNextPass(during: () => void): { restore(): void } {
    const rename = fs.renameSync
    let done = false
    const spy = spyOn(fs, 'renameSync').mockImplementation(((
      from: string,
      to: string,
    ) => {
      rename(from, to)
      if (to.endsWith('.claimed') && !done) {
        done = true
        during()
      }
    }) as never)
    return { restore: () => spy.mockRestore() }
  }

  it('removes what a finished manifest names once nothing else names it', () => {
    leftover(X)
    started(manifestOfADeadProcess([X]), { pid: deadPid(), start: '1' })
    expect(collectMountPoints()).toEqual([X])
    expect(existsSync(X)).toBe(false)
    // The manifest, its record and the claim on it went with it.
    expect(readdirSync(DIR)).toEqual([])
  })

  it('keeps a mount point named by a manifest that is published while the pass is under way', () => {
    // Nothing keeps a wrap from publishing while a pass is under way, naming a
    // path the pass is about to remove, with a sandbox starting under it.
    leftover(X)
    manifestOfADeadProcess([X])
    let published: { status: number | null; stdout: string } | undefined
    const pass = duringTheNextPass(() => {
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
        // Under its claim, which any later pass takes up.
        expect(claims()).toEqual([claimOf(manifest)])
        expect([...namedMountPoints().named]).toEqual([inside])
      } finally {
        chmodSync(readOnly, 0o755)
      }
      expect(collectMountPoints()).toEqual([inside])
      expect(readdirSync(DIR)).toEqual([])
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
        expect(claims()).toEqual([claimOf(manifest)])
      } finally {
        chmodSync(readOnly, 0o755)
      }
      // Whatever the next pass is told to release.
      expect(collectMountPoints('none')).toEqual([inside])
      expect(readdirSync(DIR)).toEqual([])
    },
  )

  it('keeps the manifest of a wrap of its own when the pass turns back half way, for the next', () => {
    leftover(X)
    const manifest = publishMountPointManifest([X], [])!.file
    // Another version of this library publishes, in a layout this one cannot
    // read, after the pass has claimed: the pass stops short of removing
    // anything.
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
    expect(claims()).toEqual([claimOf(manifest)])

    rmSync(stranger)
    expect(collectMountPoints('none')).toEqual([X])
    expect(readdirSync(DIR)).toEqual([])
  })

  it('lists the directory again before every removal of an ordinary pass', () => {
    // A sandbox about to start on a path shows as a manifest that was not there
    // when the pass began, at any point of the pass, with no time having to go
    // by: each removal is judged on a listing made just before it.
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    manifestOfADeadProcess([X, Y])
    const unlink = fs.unlinkSync
    let arrived: string | undefined
    const spy = spyOn(fs, 'unlinkSync').mockImplementation(((file: string) => {
      unlink(file)
      if (file === X && arrived === undefined) {
        // Published the moment the first mount point has gone.
        arrived = manifestOfADeadProcess([Y], {
          pid: process.pid,
          created: Date.now(),
        })
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

  it('lists by the clock, not before every removal, in a pass of many mount points', () => {
    // A directory of thousands is not listed thousands of times.
    const many = Array.from({ length: 200 }, (_, i) => join(BASE, `m${i}.lock`))
    many.forEach(leftover)
    manifestOfADeadProcess(many)
    const readdir = fs.readdirSync
    let listings = 0
    const spy = spyOn(fs, 'readdirSync').mockImplementation(((
      ...args: Parameters<typeof fs.readdirSync>
    ) => {
      if (args[0] === DIR) listings++
      return readdir(...args)
    }) as never)
    let removed: string[]
    try {
      removed = collectMountPoints()
    } finally {
      spy.mockRestore()
    }
    expect(removed.sort()).toEqual([...many].sort())
    expect(listings).toBeGreaterThan(2)
    expect(listings).toBeLessThan(many.length)
  })

  it('is live for half a second from when it was written, though its writer is gone', () => {
    // A command whose wrapping process was killed a moment ago is not refused
    // its start for that.
    leftover(X)
    const manifest = manifestOfADeadProcess([X], { created: Date.now() })
    expect(collectMountPoints()).toEqual([])
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)
  })

  // ---- a sandbox vouches for itself ----
  //
  // The command line a wrap hands out records the process it starts bubblewrap
  // in. With a record, that process alone says whether the manifest is live.

  it('is live while a process on its record runs, whoever wrote it and whatever the caller has said', () => {
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const theirs = started(manifestOfADeadProcess([X]), thisProcess())
    const own = started(publishMountPointManifest([Y], [])!.file, thisProcess())

    expect(collectMountPoints('all')).toEqual([])
    expect(collectMountPoints('all')).toEqual([])
    for (const kept of [X, Y, theirs, own, recordOf(theirs), recordOf(own)]) {
      expect(existsSync(kept)).toBe(true)
    }
    expect([...namedMountPoints().live].sort()).toEqual([X, Y].sort())
  })

  it('is finished once no process on its record runs, though the process that wrote it does', () => {
    leftover(X)
    const manifest = started(manifestOfADeadProcess([X], thisProcess()), {
      pid: deadPid(),
      start: '1',
    })
    expect([...namedMountPoints().live]).toEqual([])
    expect(collectMountPoints('none')).toEqual([X])
    expect(existsSync(manifest)).toBe(false)
    expect(existsSync(recordOf(manifest))).toBe(false)
  })

  it('tells a process from a later one with its pid by when it started', () => {
    leftover(X)
    const later = String(Number(thisProcess().start) + 1)
    started(manifestOfADeadProcess([X]), { pid: process.pid, start: later })
    expect(collectMountPoints()).toEqual([X])
  })

  it('is live while any of the runs on its record lasts', () => {
    // The same command line run again, before the first run is over or after.
    leftover(X)
    const gone = { pid: deadPid(), start: '1' }
    started(manifestOfADeadProcess([X]), gone, thisProcess(), gone)
    expect(collectMountPoints()).toEqual([])
    expect(existsSync(X)).toBe(true)
  })

  it('removes a record left without its manifest once no process on it runs', () => {
    // What a command line run after its manifest was collected leaves: it
    // records itself, and bubblewrap then finds no manifest to bind.
    const left = join(DIR, '4242-0123456789abcdef.started')
    writeFileSync(left, statLine({ pid: deadPid(), start: '1' }))
    collectMountPoints()
    expect(existsSync(left)).toBe(false)
  })

  // ---- nothing is removed but under a claim ----
  //
  // bubblewrap binds the manifest before it makes a mount point. A pass renames
  // a finished manifest before it removes what that names, so a command that
  // starts from then on fails having made nothing, and reads the directory
  // after that, for a command that started just before.

  /** Runs `at` just before the pass removes `mountPoint`. */
  function atTheRemovalOf(
    mountPoint: string,
    at: () => void,
  ): { restore(): void } {
    const unlink = fs.unlinkSync
    const spy = spyOn(fs, 'unlinkSync').mockImplementation(((file: string) => {
      if (file === mountPoint) at()
      unlink(file)
    }) as never)
    return { restore: () => spy.mockRestore() }
  }

  it('claims a finished manifest before it removes what that names', () => {
    leftover(X)
    const manifest = manifestOfADeadProcess([X])
    const seen: unknown[] = []
    const removal = atTheRemovalOf(X, () =>
      seen.push({ manifest: existsSync(manifest), claims: claims() }),
    )
    try {
      expect(collectMountPoints()).toEqual([X])
    } finally {
      removal.restore()
    }
    expect(seen).toEqual([{ manifest: false, claims: [claimOf(manifest)] }])
    expect(readdirSync(DIR)).toEqual([])
  })

  it('gives its claim back, and removes nothing, when a process has started under the manifest by then', () => {
    // The command was started between the pass reading the manifest as finished
    // and its claim: bubblewrap has bound the manifest and goes on to its mount
    // points.
    leftover(X)
    const manifest = manifestOfADeadProcess([X])
    const pass = duringTheNextPass(() => started(manifest, thisProcess()))
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      pass.restore()
    }
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)
    expect(claims()).toEqual([])
  })

  /** Claims `manifest`, as a pass does. */
  function claimed(manifest: string): string {
    const claim = join(DIR, claimOf(manifest))
    fs.renameSync(manifest, claim)
    return claim
  }

  // ---- a path is kept while any manifest that names it may have a sandbox ----

  it('keeps a path that a live manifest names too, whichever manifest the pass is collecting', () => {
    // The same project wrapped twice: both wraps name the mount point.
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const finished = manifestOfADeadProcess([X, Y])
    const live = started(manifestOfADeadProcess([X]), thisProcess())
    expect(collectMountPoints()).toEqual([Y])
    expect(existsSync(X)).toBe(true)
    expect(existsSync(finished)).toBe(false)
    expect(existsSync(live)).toBe(true)

    // It goes once that sandbox has ended too.
    started(live, { pid: deadPid(), start: '1' })
    expect(collectMountPoints()).toEqual([X])
  })

  it('keeps a path that another manifest names when a command starts under that one during the pass', () => {
    // Both read as finished, and both are claimed. The reading that follows the
    // claims finds a process on the record of one: it keeps the path for both.
    leftover(X)
    const one = manifestOfADeadProcess([X])
    const other = manifestOfADeadProcess([X])
    const pass = duringTheNextPass(() => started(other, thisProcess()))
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      pass.restore()
    }
    expect(existsSync(X)).toBe(true)
    expect(existsSync(other)).toBe(true)
    expect(existsSync(one)).toBe(false)
    expect(claims()).toEqual([])
  })

  it('keeps what a manifest at its own name names, finished or not', () => {
    // A command can start under it at any moment: only a claim refuses one.
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const refused = manifestOfADeadProcess([X])
    manifestOfADeadProcess([X, Y])
    const rename = fs.renameSync
    const spy = spyOn(fs, 'renameSync').mockImplementation(((
      from: string,
      to: string,
    ) => {
      if (from === refused) {
        throw Object.assign(new Error(`EACCES: ${from}`), { code: 'EACCES' })
      }
      rename(from, to)
    }) as never)
    try {
      expect(collectMountPoints()).toEqual([Y])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(X)).toBe(true)
    expect(existsSync(refused)).toBe(true)
  })

  // ---- any number of passes at once ----
  //
  // A pass takes no lock and waits for nobody. A claim is anybody's to act on:
  // with no process on its record nothing can start under it again.

  it('collects on a claim that another pass made, or that a killed one left', () => {
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    // Though its writer runs: whoever claimed it knew its command to be over.
    const claim = claimed(manifestOfADeadProcess([X], thisProcess()))
    manifestOfADeadProcess([X, Y])
    expect([...namedMountPoints().named].sort()).toEqual([X, Y].sort())
    expect(live()).toEqual([])
    expect(collectMountPoints().sort()).toEqual([X, Y].sort())
    expect(existsSync(claim)).toBe(false)
    expect(readdirSync(DIR)).toEqual([])
  })

  it('keeps what a claimed manifest names while a process on its record runs, and leaves the claim to the pass that made it', () => {
    leftover(X)
    const claim = claimed(started(manifestOfADeadProcess([X]), thisProcess()))
    expect(live()).toEqual([X])
    expect(collectMountPoints()).toEqual([])
    expect(existsSync(X)).toBe(true)
    expect(claims()).toEqual([basename(claim)])
  })

  it('leaves a manifest and its record that were given back while it removed what they name', () => {
    // The pass that made the claim found a process on the record after this one
    // had read it, and a sandbox now runs under the manifest again.
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const manifest = manifestOfADeadProcess([X, Y])
    const claim = claimed(manifest)
    const removal = atTheRemovalOf(X, () => {
      fs.renameSync(claim, manifest)
      started(manifest, thisProcess())
    })
    try {
      // Y stays: the manifest is at its own name by the time Y's turn comes.
      expect(collectMountPoints()).toEqual([X])
    } finally {
      removal.restore()
    }
    expect(existsSync(Y)).toBe(true)
    expect(readdirSync(DIR).sort()).toEqual(
      [basename(manifest), basename(recordOf(manifest))].sort(),
    )
  })

  it('finds a manifest that is claimed, or given back, between being listed and being opened', () => {
    // Taken for gone, it would name nothing: a wrap would take its mount point
    // for the caller's own file, and a pass would remove what it names.
    leftover(X)
    const manifest = started(manifestOfADeadProcess([X]), thisProcess())
    const open = fs.openSync
    let claim: string | undefined
    const spy = spyOn(fs, 'openSync').mockImplementation(((
      file: string,
      ...rest: unknown[]
    ) => {
      if (file === manifest && claim === undefined) {
        claim = claimed(manifest)
      } else if (file === claim && !existsSync(manifest)) {
        fs.renameSync(claim, manifest)
      }
      return (open as (...args: unknown[]) => number)(file, ...rest)
    }) as never)
    try {
      expect([...namedMountPoints().named]).toEqual([X])
      expect(claim).toBeDefined()
      expect(live()).toEqual([X])
      expect(collectMountPoints()).toEqual([])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(X)).toBe(true)
  })

  it('removes nothing while a listed manifest keeps being gone when it is opened', () => {
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    manifestOfADeadProcess([Y])
    const elusive = started(manifestOfADeadProcess([X]), thisProcess())
    const open = fs.openSync
    const spy = spyOn(fs, 'openSync').mockImplementation(((
      file: string,
      ...rest: unknown[]
    ) => {
      if (file === elusive) {
        throw Object.assign(new Error(`ENOENT: ${file}`), { code: 'ENOENT' })
      }
      return (open as (...args: unknown[]) => number)(file, ...rest)
    }) as never)
    try {
      // What it names cannot be listed, so what any other names is held.
      expect(live()).toEqual([Y])
      expect(collectMountPoints()).toEqual([])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(Y)).toBe(true)
  })

  it('leaves a claim on a manifest written in another PID namespace', () => {
    leftover(X)
    const claim = claimed(manifestOfADeadProcess([X], { ns: 'pid:[1]' }))
    expect(collectMountPoints()).toEqual([])
    expect(existsSync(claim)).toBe(true)
    expect(existsSync(X)).toBe(true)
  })

  it('never blocks the thread it runs on', () => {
    // A clean-up runs on its caller's one thread, after every command.
    leftover(X)
    claimed(manifestOfADeadProcess([X]))
    manifestOfADeadProcess([X])
    const wait = spyOn(Atomics, 'wait')
    try {
      expect(collectMountPoints()).toEqual([X])
      expect(wait).not.toHaveBeenCalled()
    } finally {
      wait.mockRestore()
    }
  })

  // ---- what cannot be told is live ----
  //
  // Only a process that is gone says its sandbox has ended. A sandboxed command
  // can use up what this user may open or map, so a read that fails in a pass
  // must never end in a removal.

  /** Has reading `target` fail with `code`: opening it, or reading what was opened. */
  function failing(
    target: string,
    code: string,
    at: 'open' | 'read' = 'open',
  ): { restore(): void } {
    const fail = (): never => {
      throw Object.assign(new Error(`${code}: ${target}`), { code })
    }
    const inode = existsSync(target) ? statSync(target).ino : undefined
    const open = fs.openSync
    const read = fs.readFileSync
    const fstat = fs.fstatSync
    const spies = [
      spyOn(fs, 'openSync').mockImplementation(((
        file: unknown,
        ...rest: unknown[]
      ) =>
        at === 'open' && file === target
          ? fail()
          : (open as (...args: unknown[]) => number)(file, ...rest)) as never),
      spyOn(fs, 'readFileSync').mockImplementation(((
        file: unknown,
        options: unknown,
      ) =>
        file === target ||
        (at === 'read' && typeof file === 'number' && fstat(file).ino === inode)
          ? fail()
          : (read as (f: unknown, o: unknown) => unknown)(
              file,
              options,
            )) as never),
    ]
    return { restore: () => spies.forEach(spy => spy.mockRestore()) }
  }

  /** What a pass removes, and the set a caller is given, with that in place. */
  function withThat(injected: { restore(): void }): {
    removed: string[]
    held: string[]
  } {
    try {
      return { held: live(), removed: collectMountPoints() }
    } finally {
      injected.restore()
    }
  }

  const NOTHING_REMOVED = { removed: [], held: [expect.any(String)] }

  for (const code of ['EACCES', 'EMFILE', 'ENFILE', 'ENOMEM', 'EIO']) {
    it(`removes nothing when it cannot ask after the process on a record: ${code}`, () => {
      leftover(X)
      const gone = { pid: deadPid(), start: '1' }
      started(manifestOfADeadProcess([X]), gone)
      expect(withThat(failing(`/proc/${gone.pid}/stat`, code))).toEqual(
        NOTHING_REMOVED,
      )
      expect(existsSync(X)).toBe(true)
    })

    it(`removes nothing when it cannot ask after the writer of a manifest with no record: ${code}`, () => {
      leftover(X)
      const gone = { pid: deadPid(), start: '1' }
      manifestOfADeadProcess([X], gone)
      expect(withThat(failing(`/proc/${gone.pid}/stat`, code))).toEqual(
        NOTHING_REMOVED,
      )
      expect(existsSync(X)).toBe(true)
    })

    for (const at of ['open', 'read'] as const) {
      it(`removes nothing at all when a manifest cannot be read: ${code} at the ${at}`, () => {
        const Y = join(BASE, 'second.lock')
        leftover(X)
        leftover(Y)
        manifestOfADeadProcess([Y])
        const manifest = manifestOfADeadProcess([X])
        // However old it is, and with no process on its record: this is no
        // file to drop for being unreadable.
        const hoursAgo = new Date(Date.now() - 2 * 3600 * 1000)
        utimesSync(manifest, hoursAgo, hoursAgo)
        // What it names cannot be listed, so what any other names is held.
        expect(withThat(failing(manifest, code, at))).toEqual({
          removed: [],
          held: [Y],
        })
        expect(existsSync(X)).toBe(true)
        expect(existsSync(manifest)).toBe(true)
      })

      it(`keeps what a manifest names when its record cannot be read: ${code} at the ${at}`, () => {
        leftover(X)
        const manifest = started(manifestOfADeadProcess([X]), {
          pid: deadPid(),
          start: '1',
        })
        expect(withThat(failing(recordOf(manifest), code, at))).toEqual(
          NOTHING_REMOVED,
        )
        expect(existsSync(X)).toBe(true)
      })
    }
  }

  it('removes nothing when what it reads of the process on a record is cut short', () => {
    leftover(X)
    started(manifestOfADeadProcess([X]), thisProcess())
    const read = fs.readFileSync
    const spy = spyOn(fs, 'readFileSync').mockImplementation(((
      file: unknown,
      options: unknown,
    ) => {
      const whole = (read as (f: unknown, o: unknown) => unknown)(file, options)
      return file === `/proc/${process.pid}/stat`
        ? String(whole).split(' ').slice(0, 12).join(' ')
        : whole
    }) as never)
    expect(withThat({ restore: () => spy.mockRestore() })).toEqual(
      NOTHING_REMOVED,
    )
  })

  const gone = (): string => statLine({ pid: deadPid(), start: '1' })
  const notARecord: [string, (record: string) => void][] = [
    ['empty, as between the shell making it and writing to it', r => write(r)],
    ['cut short of its end of line', r => write(r, gone().slice(0, -1))],
    ['cut short of the start time', r => write(r, `${gone().slice(0, 30)}\n`)],
    ['not the line of a process', r => write(r, 'ended\n')],
    [
      'a line of a process and then something else',
      r => write(r, `${gone()}?\n`),
    ],
    [
      'larger than a record can be',
      r => write(r, gone().repeat(1 + Math.ceil(65536 / gone().length))),
    ],
    [
      'a link to the record of a process that is gone',
      r => {
        write(join(BASE, 'elsewhere.started'), gone())
        symlinkSync(join(BASE, 'elsewhere.started'), r)
      },
    ],
    ['a directory', r => mkdirSync(r)],
    [
      'a FIFO nobody writes to',
      r => expect(spawnSync('mkfifo', [r]).status).toBe(0),
    ],
  ]
  function write(file: string, text = ''): void {
    writeFileSync(file, text, { mode: 0o600 })
  }
  for (const [what, plant] of notARecord) {
    it(`keeps what a manifest names while its record is ${what}`, () => {
      leftover(X)
      const manifest = manifestOfADeadProcess([X])
      plant(recordOf(manifest))
      // In a process of its own: opening a FIFO to read waits for a writer, on
      // the one thread there is.
      const looked = inAChild(
        `console.log(JSON.stringify({ held: [...m.liveMountPoints()], removed: m.collectMountPoints() }))`,
      )
      expect(looked.status).toBe(0)
      expect(looked.ms).toBeLessThan(AT_ONCE_MS)
      expect(JSON.parse(looked.stdout)).toEqual({ held: [X], removed: [] })
      expect(existsSync(manifest)).toBe(true)
    }, 15000)
  }

  it("keeps what a manifest names while its record is somebody else's", () => {
    leftover(X)
    const manifest = started(manifestOfADeadProcess([X]), {
      pid: deadPid(),
      start: '1',
    })
    const theirs = asSomebodyElses(recordOf(manifest))
    expect(withThat(theirs)).toEqual(NOTHING_REMOVED)
    expect(existsSync(X)).toBe(true)
  })

  it('removes nothing while a process that runs is on a record whose manifest is not to be found', () => {
    // A claim is a rename, and a rename can hide a name from a listing that is
    // under way: the manifest may be there all the same.
    leftover(X)
    manifestOfADeadProcess([X])
    const record = join(DIR, '4242-0123456789abcdef.started')
    writeFileSync(record, statLine(thisProcess()))
    // However old it is.
    const hoursAgo = new Date(Date.now() - 2 * 3600 * 1000)
    utimesSync(record, hoursAgo, hoursAgo)
    expect(collectMountPoints()).toEqual([])
    expect(existsSync(X)).toBe(true)
    expect(existsSync(record)).toBe(true)
  })

  it('removes nothing when the manifests cannot be listed', () => {
    leftover(X)
    manifestOfADeadProcess([X])
    const readdir = fs.readdirSync
    const spy = spyOn(fs, 'readdirSync').mockImplementation(((
      dir: unknown,
      options: unknown,
    ) => {
      if (dir === DIR) {
        throw Object.assign(new Error(`EMFILE: ${DIR}`), { code: 'EMFILE' })
      }
      return (readdir as (d: unknown, o: unknown) => unknown)(dir, options)
    }) as never)
    try {
      expect(collectMountPoints()).toEqual([])
    } finally {
      spy.mockRestore()
    }
    expect(existsSync(X)).toBe(true)
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
    const old = [join(DIR, '4242-0123456789abcdef.json.tmp')]
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
  // /proc/PID is local to a PID namespace. From another namespace a running
  // sandbox's manifest looks like one a dead process left.

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
      'kept',
      { ns: undefined, created: Date.now() - 2 * 3600 * 1000 },
    ],
    ['written in this PID namespace', 'collected', {}],
  ] as const)(
    'a manifest %s, with no writer and no process on record to be seen, is %s',
    (_what, outcome, fields) => {
      leftover(X)
      const manifest = manifestOfADeadProcess([X], fields)
      collectMountPoints()
      expect(existsSync(X)).toBe(outcome === 'kept')
      expect(existsSync(manifest)).toBe(outcome === 'kept')
    },
  )

  it('is live when written in another PID namespace, whatever process is on its record', () => {
    // The pid on the record was given in that namespace too.
    leftover(X)
    const manifest = started(manifestOfADeadProcess([X], { ns: 'pid:[1]' }), {
      pid: deadPid(),
      start: '1',
    })
    expect(collectMountPoints()).toEqual([])
    expect(existsSync(X)).toBe(true)
    expect(existsSync(manifest)).toBe(true)
  })

  // ---- where the manifests are kept --------------------------------------

  it.if(BWRAP_CAN_NAMESPACE)(
    'are never kept under /dev, which the sandbox mounts afresh over them',
    () => {
      // The wrap mounts a new /dev after every bind: a manifest directory under
      // /dev could be neither bound nor kept out of the command's reach. Looked
      // at with a /dev/shm of the child's own, not the one every process has.
      const SHM = '/dev/shm'
      const launcher = ['bwrap', '--dev-bind', '/', '/', '--tmpfs', SHM, '--']
      const publishAndList = `const { readdirSync } = await import('node:fs')\nconsole.log(JSON.stringify({ manifest: m.publishMountPointManifest(['/nonexistent/x'], []) ?? null, made: readdirSync(${JSON.stringify(SHM)}) }))`
      const fellBack = inAChild(publishAndList, {
        launcher,
        env: { XDG_RUNTIME_DIR: SHM },
      })
      expect(fellBack.status).toBe(0)
      const recorded = JSON.parse(fellBack.stdout) as {
        manifest: { file: string }
        made: string[]
      }
      expect(recorded.manifest.file.startsWith(`${TMP}/`)).toBe(true)
      expect(recorded.made).toEqual([])

      // With nowhere else to go it records nothing, rather than somewhere
      // bubblewrap cannot reach.
      const nowhere = inAChild(publishAndList, {
        launcher,
        env: { XDG_RUNTIME_DIR: undefined, TMPDIR: SHM },
      })
      expect(nowhere.status).toBe(0)
      expect(JSON.parse(nowhere.stdout)).toEqual({ manifest: null, made: [] })
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
    const published = inAChild(PUBLISH, { env: { XDG_RUNTIME_DIR: undefined } })
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

  // ---- which directory is believed ----
  //
  // A pass removes what it finds named in the directory, so the directory has
  // to be the user's alone, and is looked at again at every use.

  /** Has `file` look like another user's: nothing here can make one. */
  function asSomebodyElses(file: string): { restore(): void } {
    const inode = lstatSync(file).ino
    const spies = (['lstatSync', 'fstatSync'] as const).map(name => {
      const real = fs[name] as (f: unknown, o: unknown) => fs.Stats
      return spyOn(fs, name).mockImplementation(((
        target: unknown,
        options: unknown,
      ) => {
        const stat = real(target, options)
        if (stat.ino !== inode) return stat
        const theirs = Object.create(
          Object.getPrototypeOf(stat) as object,
        ) as fs.Stats
        return Object.assign(theirs, stat, { uid: stat.uid + 1 })
      }) as never)
    })
    return { restore: () => spies.forEach(spy => spy.mockRestore()) }
  }

  /** Where this process, having settled on nothing yet, records X. */
  function recordedIn(): string {
    forgetMountPointManifestDirectory()
    return dirname(publishMountPointManifest([X], [])!.file)
  }

  it("are not kept in a directory that is somebody else's", () => {
    const theirs = asSomebodyElses(DIR)
    try {
      expect(recordedIn()).toBe(
        join(tmpdir(), `srt-mount-points-${process.getuid!()}`),
      )
    } finally {
      theirs.restore()
      forgetMountPointManifestDirectory()
    }
    expect(readdirSync(DIR)).toEqual([])
  })

  it("are kept in a directory that others could read or write only once it has been made the user's alone", () => {
    chmodSync(DIR, 0o755)
    expect(recordedIn()).toBe(DIR)
    expect(statSync(DIR).mode & 0o777).toBe(0o700)
  })

  it("are not kept in a directory that cannot be made the user's alone", () => {
    chmodSync(DIR, 0o750)
    const spy = spyOn(fs, 'fchmodSync').mockImplementation((() => {
      throw Object.assign(new Error('EPERM'), { code: 'EPERM' })
    }) as never)
    try {
      expect(recordedIn()).not.toBe(DIR)
    } finally {
      spy.mockRestore()
      forgetMountPointManifestDirectory()
    }
    expect(readdirSync(DIR)).toEqual([])
  })

  it('are kept in a directory that is looked at again at every use', () => {
    expect(recordedIn()).toBe(DIR)
    rmSync(DIR, { recursive: true })

    // Opened up since: made the user's alone again before it is used.
    mkdirSync(DIR, { mode: 0o777 })
    chmodSync(DIR, 0o777)
    expect(dirname(publishMountPointManifest([X], [])!.file)).toBe(DIR)
    expect(statSync(DIR).mode & 0o777).toBe(0o700)
    rmSync(DIR, { recursive: true })

    // Swapped for a link since: not followed, and what it leads to left alone.
    const target = join(BASE, 'somebody-elses')
    mkdirSync(target, { mode: 0o700 })
    symlinkSync(target, DIR)
    try {
      expect(dirname(publishMountPointManifest([X], [])!.file)).not.toBe(DIR)
      expect(readdirSync(target)).toEqual([])
    } finally {
      rmSync(DIR)
      mkdirSync(DIR, { mode: 0o700 })
      forgetMountPointManifestDirectory()
    }
  })

  // ---- with nowhere to record ----
  //
  // No other process can know of these mount points, so the process that made
  // them removes them itself, once none of its wraps is outstanding.

  it.if(NOT_ROOT)(
    'keeps in memory what it could record nowhere, and removes it at its own clean-up',
    () => {
      const directory = join(BASE, 'empty-directory')
      const source = join(BASE, 'source')
      const readOnly = join(BASE, 'read-only-tmp')
      leftover(X)
      mkdirSync(directory)
      mkdirSync(source, { mode: 0o700 })
      mkdirSync(readOnly, { mode: 0o500 })
      const nowhere = inAChild(
        [
          `const at = ${JSON.stringify({ X, directory, source })}`,
          `const { existsSync } = await import('node:fs')`,
          `const there = () => [at.X, at.directory, at.source].map(p => existsSync(p))`,
          `const published = m.publishMountPointManifest([at.X, at.directory], [at.source]) ?? null`,
          `const named = m.namedMountPoints()`,
          `const held = [...m.liveMountPoints()].sort()`,
          `const some = { removed: m.collectMountPoints('none'), there: there() }`,
          `const all = { removed: m.collectMountPoints('all').sort(), there: there() }`,
          `console.log(JSON.stringify({ published, named: [...named.named].sort(), live: [...named.live].sort(), held, some, all, again: m.collectMountPoints('all') }))`,
        ].join('\n'),
        // No runtime directory, and nothing can be made under the temp dir.
        { env: { XDG_RUNTIME_DIR: undefined, TMPDIR: readOnly } },
      )
      expect(nowhere.status).toBe(0)
      expect(JSON.parse(nowhere.stdout)).toEqual({
        published: null,
        named: [X, directory].sort(),
        live: [X, directory].sort(),
        held: [X, directory].sort(),
        some: { removed: [], there: [true, true, true] },
        all: {
          removed: [X, directory, source].sort(),
          there: [false, false, false],
        },
        again: [],
      })
    },
    15000,
  )

  it('keeps what it could not record while a manifest of another process names it, where there is a directory to go by', () => {
    // The manifest could not be written, as with the temp dir full, which a
    // sandboxed command can bring about.
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    started(manifestOfADeadProcess([X]), thisProcess())
    const write = fs.writeFileSync
    const spy = spyOn(fs, 'writeFileSync').mockImplementation(((
      file: unknown,
      ...rest: unknown[]
    ) => {
      if (String(file).endsWith('.json.tmp')) {
        throw Object.assign(new Error('ENOSPC'), { code: 'ENOSPC' })
      }
      return (write as (...args: unknown[]) => void)(file, ...rest)
    }) as never)
    try {
      expect(publishMountPointManifest([X, Y], [])).toBeUndefined()
    } finally {
      spy.mockRestore()
    }
    expect([...namedMountPoints().named].sort()).toEqual([X, Y].sort())
    expect(collectMountPoints('none')).toEqual([])
    expect(collectMountPoints('all')).toEqual([Y])
    expect(existsSync(X)).toBe(true)
  })

  // ---- what is read as a manifest ----
  //
  // Only a regular file of the user's, of a size a manifest can have, is read:
  // a link is not followed and a FIFO is not opened. What is there instead
  // names paths nobody can list, so while it may have a sandbox under it
  // nothing at all is removed.

  /** Two hours old: past the hour for which what is no manifest counts as live. */
  function aged(file: string): string {
    const hoursAgo = new Date(Date.now() - 2 * 3600 * 1000)
    lutimesSync(file, hoursAgo, hoursAgo)
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
        symlinkSync(elsewhere, name)
      },
    ],
    [
      'a manifest of more than a mebibyte',
      (name, paths) =>
        writeFileSync(
          name,
          finishedManifestText(paths) + ' '.repeat(1024 * 1024),
          { mode: 0o600 },
        ),
    ],
    [
      'a manifest cut short',
      (name, paths) =>
        writeFileSync(name, finishedManifestText(paths).slice(0, -1)),
    ],
    [
      'a manifest of another version',
      (name, paths) =>
        writeFileSync(
          name,
          finishedManifestText(paths).replace('"version":1', '"version":2'),
        ),
    ],
    ['a directory', name => mkdirSync(name)],
    [
      'a FIFO nobody writes to',
      name => expect(spawnSync('mkfifo', [name]).status).toBe(0),
    ],
  ]
  for (const [what, plant] of notAManifest) {
    it(`removes nothing beside ${what} until it is an hour old, and passes over it then`, () => {
      const Y = join(BASE, 'second.lock')
      leftover(X)
      leftover(Y)
      const junk = join(DIR, '4242-0123456789abcdef.json')
      plant(junk, [X])
      manifestOfADeadProcess([Y])
      // In a process of its own: opening a FIFO to read waits for a writer, on
      // the one thread there is.
      const look = (): unknown => {
        const looked = inAChild(
          `console.log(JSON.stringify({ named: [...m.namedMountPoints().named], held: [...m.liveMountPoints()], removed: m.collectMountPoints() }))`,
        )
        expect(looked.status).toBe(0)
        expect(looked.ms).toBeLessThan(AT_ONCE_MS)
        return JSON.parse(looked.stdout)
      }
      // It names nothing that can be read, and may name anything.
      expect(look()).toEqual({ named: [Y], held: [Y], removed: [] })

      // Nor while a process is on its record, however old it is.
      aged(junk)
      writeFileSync(recordOf(junk), statLine(thisProcess()))
      expect(look()).toEqual({ named: [Y], held: [Y], removed: [] })

      rmSync(recordOf(junk))
      expect(look()).toEqual({ named: [Y], held: [], removed: [Y] })
      expect(existsSync(X)).toBe(true)
      // Dropped, where it is a file that can be.
      expect(existsSync(junk)).toBe(what === 'a directory')
    }, 30000)
  }

  it("removes nothing beside a manifest that is somebody else's until it is an hour old, and passes over it then", () => {
    const Y = join(BASE, 'second.lock')
    leftover(X)
    leftover(Y)
    const junk = manifestOfADeadProcess([X])
    manifestOfADeadProcess([Y])
    const theirs = asSomebodyElses(junk)
    try {
      expect([...namedMountPoints().named]).toEqual([Y])
      expect(collectMountPoints()).toEqual([])
      aged(junk)
      expect(collectMountPoints()).toEqual([Y])
    } finally {
      theirs.restore()
    }
    expect(existsSync(X)).toBe(true)
  })

  // ---- which mount points a running sandbox relies on ----
  //
  // A caller that removes paths itself after a command can ask first which to
  // leave out. What it is told to leave out is never more than an empty
  // placeholder.

  /** The set, as a sorted list. */
  function live(): string[] {
    return [...liveMountPoints()].sort()
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

  it('holds what a finished manifest names only while a process on its record runs', () => {
    leftover(X)
    const manifest = manifestOfADeadProcess([X])
    expect(live()).toEqual([])
    started(manifest, { pid: deadPid(), start: '1' })
    expect(live()).toEqual([])
    started(manifest, thisProcess())
    expect(live()).toEqual([X])
  })

  it('holds what any manifest names while something in the directory cannot be read, and of that only what looks like a mount point', () => {
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
  })

  it('is one listing of the directory, and changes nothing in it', () => {
    leftover(X)
    publishMountPointManifest([X], [])
    started(manifestOfADeadProcess([join(BASE, 'other.lock')]), {
      pid: deadPid(),
      start: '1',
    })
    // What a pass would take away: a record whose manifest and process are gone.
    writeFileSync(
      join(DIR, '4242-0123456789abcdef.started'),
      statLine({ pid: deadPid(), start: '1' }),
    )
    const before = readdirSync(DIR).sort()

    const readdir = spyOn(fs, 'readdirSync')
    const rename = spyOn(fs, 'renameSync')
    let listed: string[]
    let listings: number
    try {
      listed = live()
      listings = readdir.mock.calls.filter(([dir]) => dir === DIR).length
      expect(rename).not.toHaveBeenCalled()
    } finally {
      readdir.mockRestore()
      rename.mockRestore()
    }
    expect(listed).toEqual([X])
    expect(listings).toBe(1)
    expect(readdirSync(DIR).sort()).toEqual(before)
  })

  it('makes no manifest directory where there is none, and holds nothing then', () => {
    const run = join(BASE, 'run')
    mkdirSync(run, { mode: 0o700 })
    const looked = inAChild(
      `console.log(JSON.stringify([...m.liveMountPoints()]))`,
      { env: { XDG_RUNTIME_DIR: run } },
    )
    expect(looked.status).toBe(0)
    expect(JSON.parse(looked.stdout)).toEqual([])
    expect(readdirSync(run)).toEqual([])
    expect(readdirSync(TMP)).toEqual([])
  })

  it('reads the directory a process without a runtime directory keeps, where that is the one there is', () => {
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
    const run = join(BASE, 'run')
    mkdirSync(run, { mode: 0o700 })
    const looked = inAChild(
      `console.log(JSON.stringify([...m.liveMountPoints()]))`,
      { env: { XDG_RUNTIME_DIR: run } },
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
