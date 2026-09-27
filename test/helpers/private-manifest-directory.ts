import { afterAll, beforeAll } from 'bun:test'
import {
  chmodSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  realpathSync,
  rmSync,
  writeFileSync,
} from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, extname, join } from 'node:path'
import {
  type ManifestDirectoryPlaces,
  setMountPointManifestPlacesForTesting,
} from '../../src/sandbox/bwrap-mount-manifests.js'
import { cleanupBwrapMountPoints } from '../../src/sandbox/linux-sandbox-utils.js'

const REPOSITORY = join(import.meta.dir, '../..')
const SEAM = join(REPOSITORY, 'src/sandbox/bwrap-mount-manifests.ts')

/**
 * The manifests of every srt process of a user live in a few directories that
 * are worked out from the user id: `/run/user/UID/srt-mount-points` and
 * `/tmp/srt-mount-points-UID`, and after those what the environment names.
 * Every wrap makes and binds them, and every clean-up reads, judges and
 * removes what is in them. A test that did so in the real ones would be doing
 * it to whatever else that user is running on the machine, and be failed by
 * it in turn, and nothing in the environment moves a process away from them.
 * So no test looks there:
 *
 * - in the test process, directories of the test's own stand in for all four
 *   places, through the seam the module has for it
 *   ({@link isolateManifestDirectoriesForTheRun} for every test file of the
 *   run, {@link usePrivateManifestDirectory} for a `describe` that wants them
 *   to itself);
 * - a child process that loads the library from a script is given a module to
 *   load that puts the same stand-ins in place first ({@link isolatedModule}),
 *   and one that runs the command line tool a program that does
 *   ({@link isolatedProgram});
 * - a child process that is to work the directories out for itself, from the
 *   real names, runs in a mount namespace of its own in which the stand-ins
 *   are bound over `/tmp` and `/run/user` ({@link inPrivateNamespace}).
 *
 * All of it is bubblewrap's, which is Linux's: on any other platform the
 * library keeps no manifest anywhere, nothing is put in the place of
 * anything, and a child process is given the module or the program itself.
 */
type Places = ManifestDirectoryPlaces

const onLinux = process.platform === 'linux'

type PrivatePlaces = {
  /** Holds the stand-ins, and what is made for child processes to load. */
  base: string
  places: Places
}

// Every base that was made and not removed yet, for the end of the run: a
// `describe` that is skipped is read all the same, and never torn down.
const bases = new Set<string>()

/**
 * Directories of the caller's own to stand in for the four places. The
 * runtime directory is named after the user id under its parent, as the real
 * one is, so that the parent can be bound over `/run/user`. Nothing stands in
 * for `$XDG_RUNTIME_DIR`, which is as if it were not set, and the temp dir
 * the environment names is the one that stands in for `/tmp`.
 */
function makePlaces(): PrivatePlaces {
  const base = realpathSync(mkdtempSync(join(tmpdir(), 'srt-test-places-')))
  bases.add(base)
  const runtimeDir = join(base, 'run', String(process.getuid?.() ?? 0))
  const tempDir = join(base, 'tmp')
  mkdirSync(runtimeDir, { recursive: true })
  chmodSync(runtimeDir, 0o700)
  mkdirSync(tempDir)
  chmodSync(tempDir, 0o1777)
  return {
    base,
    places: {
      runtimeDir,
      tempDir,
      environmentRuntimeDir: undefined,
      environmentTempDir: tempDir,
    },
  }
}

function removePlaces(made: PrivatePlaces): void {
  rmSync(made.base, { recursive: true, force: true })
  bases.delete(made.base)
}

/** `places` as source text, with what is not set spelled out. */
function sourceOf(places: Partial<Places>): string {
  const fields = Object.entries(places).map(
    ([name, value]) =>
      `${name}: ${value === undefined ? 'undefined' : JSON.stringify(value)}`,
  )
  return `{ ${fields.join(', ')} }`
}

let filesMade = 0

/**
 * A file for a child process to load in place of `target`, which puts
 * `places` in place and then is `target`: a module of the sources, which it
 * gives again, or the command line tool, from the sources or as it was built,
 * which it runs. The tool's seam is the one beside it.
 *
 * The stand-ins are in place before the child does anything with what it has
 * loaded. A module's imports are evaluated before its own body, and the body
 * is the call to the seam; a program starts work as it is loaded, so it is
 * loaded after the call.
 */
function isolatedFile(
  made: PrivatePlaces,
  target: string,
  places: Partial<Places>,
  kind: 'module' | 'program',
): string {
  const built = extname(target) !== '.ts'
  const seam =
    kind === 'module'
      ? SEAM
      : join(
          dirname(target),
          'sandbox',
          `bwrap-mount-manifests${extname(target)}`,
        )
  const file = join(
    made.base,
    `isolated-${filesMade++}${built ? '.mjs' : '.ts'}`,
  )
  writeFileSync(
    file,
    [
      `import { setMountPointManifestPlacesForTesting } from ${JSON.stringify(seam)}`,
      `setMountPointManifestPlacesForTesting(${sourceOf(places)})`,
      kind === 'module'
        ? `export * from ${JSON.stringify(target)}`
        : `await import(${JSON.stringify(target)})`,
      '',
    ].join('\n'),
  )
  return file
}

// What stands in for the real places in every test file of the run, which a
// `describe` with stand-ins of its own puts back when it is done.
let placesOfTheRun: PrivatePlaces | undefined

/**
 * Puts stand-ins in place for the whole run: most suites wrap a command
 * somewhere, and none of them is to make, bind or collect in the user's real
 * directories for it. The test runner's preload does it before any test file
 * is loaded, and takes the stand-ins away after the last one
 * ({@link removeManifestDirectoriesOfTheRun}).
 */
export function isolateManifestDirectoriesForTheRun(): void {
  if (onLinux && placesOfTheRun === undefined) {
    placesOfTheRun = makePlaces()
    setMountPointManifestPlacesForTesting(placesOfTheRun.places)
  }
}

/**
 * Removes every stand-in that is still there. They stay in place in the
 * module, so that nothing that still runs finds the real ones.
 */
export function removeManifestDirectoriesOfTheRun(): void {
  for (const left of bases) {
    rmSync(left, { recursive: true, force: true })
  }
  bases.clear()
}

/** The stand-ins of the run, which are put in place if they were not. */
function ofTheRun(): PrivatePlaces {
  isolateManifestDirectoriesForTheRun()
  return placesOfTheRun!
}

/**
 * The path of a module for a child process to load in place of `module`, with
 * the stand-ins of the run in place, or with `places` where the child is to
 * look somewhere else. A place that is left out of `places` is the real one
 * for that child: what its environment says, for the last two.
 */
export function isolatedModule(
  module: string,
  places?: Partial<Places>,
): string {
  if (!onLinux) {
    return module
  }
  const run = ofTheRun()
  return isolatedFile(run, module, places ?? run.places, 'module')
}

/**
 * The path of a program for a child process to run in place of `program`, the
 * command line tool as it is in the sources or as it was built, with the
 * stand-ins of the run in place.
 */
export function isolatedProgram(program: string): string {
  if (!onLinux) {
    return program
  }
  const run = ofTheRun()
  return isolatedFile(run, program, run.places, 'program')
}

/**
 * The start of a command line that runs what follows it in a mount namespace
 * of its own, in which `places.tempDir` is bound over `/tmp` and the parent of
 * `places.runtimeDir` over `/run/user`: for a child process that is to work
 * the directories out for itself, from the real names, without reaching the
 * real ones. Whatever is in `keep` is bound back where it is, for what the
 * child needs that lies under the real `/tmp`, and so are this repository and
 * the runtime where they lie there. No PID namespace, so `/proc/locks` and
 * the pids in it are the test's own.
 *
 * Needs a bubblewrap that can make a namespace (see `bwrapCanNamespace`).
 */
export function inPrivateNamespace(
  places: Pick<Places, 'runtimeDir' | 'tempDir'>,
  keep: readonly string[] = [],
): string[] {
  const needed = [REPOSITORY, dirname(process.execPath)].filter(dir =>
    dir.startsWith('/tmp/'),
  )
  return [
    'bwrap',
    '--dev-bind',
    '/',
    '/',
    '--bind',
    places.tempDir,
    '/tmp',
    // Where there is no /run/user there is no runtime directory to reach.
    ...(existsSync('/run/user')
      ? ['--bind', dirname(places.runtimeDir), '/run/user']
      : []),
    ...[...needed, ...keep].flatMap(kept => ['--bind', kept, kept]),
    '--',
  ]
}

/**
 * Gives the enclosing `describe` directories of its own for the mount point
 * manifests, for as long as its tests run: a test that lists the manifests,
 * attacks them from inside a sandbox or asserts on what is left of them needs
 * to be the only one that writes there.
 *
 * It also starts the `describe` with no wrap of this process outstanding, and
 * leaves it so. The library counts the wraps it has handed out and releases
 * nothing of this process's until each has been cleaned up after; the count is
 * the module's, shared by every test file of one run, and other suites wrap
 * without cleaning up. A test that expects one clean-up to take its mount point
 * away would otherwise pass or fail by which file ran before it.
 *
 * Call it inside the `describe` callback. Returns:
 * - `manifestDir()`, where this process's manifests go: under the runtime
 *   directory, the first place looked in;
 * - `places()`, the stand-ins themselves;
 * - `isolated(module, places)`, which is {@link isolatedModule} with the
 *   stand-ins of this `describe`.
 */
export function usePrivateManifestDirectory(): {
  manifestDir(): string
  places(): Places
  isolated(module: string, places?: Partial<Places>): string
} {
  let made: PrivatePlaces | undefined
  // Made on first use, which may be while the `describe` is being read, for
  // the module a child is to load.
  const own = (): PrivatePlaces => (made ??= makePlaces())

  beforeAll(() => {
    if (!onLinux) {
      return
    }
    // In the directories the earlier suites used, before they are left
    // behind.
    cleanupBwrapMountPoints({ force: true })
    setMountPointManifestPlacesForTesting(own().places)
  })

  afterAll(() => {
    if (!onLinux) {
      return
    }
    cleanupBwrapMountPoints({ force: true })
    setMountPointManifestPlacesForTesting(placesOfTheRun?.places)
    if (made !== undefined) {
      removePlaces(made)
      made = undefined
    }
  })

  return {
    manifestDir: () => join(own().places.runtimeDir, 'srt-mount-points'),
    places: () => own().places,
    isolated: (module, places) =>
      onLinux
        ? isolatedFile(own(), module, places ?? own().places, 'module')
        : module,
  }
}
