import * as fs from 'node:fs'
import * as path from 'node:path'
import { fileURLToPath } from 'node:url'
import {
  containsGlobCharsForPlatform,
  isAtOrUnder,
  normalizePathForSandbox,
  pathSpellings,
} from './sandbox-utils.js'

/**
 * The library's own files, as a thing to write-deny.
 *
 * The host side of the library runs outside any sandbox, so it must not
 * execute a file the wrapped command may write. Installed as a dependency,
 * the library lives in `<project>/node_modules/`, and the project is usually
 * what `allowWrite` names: a wrapped command could rewrite `dist/*.js` here,
 * the bundled seccomp helper or a package this one loads, and the next `srt`
 * run would execute the result unsandboxed.
 *
 * So every wrapped command is denied, inside the paths it may write:
 *
 * - the package's own directory and that of every package it depends on at
 *   run time, found the way the module loader finds them;
 * - every place the loader looks for one of those BEFORE where it is found,
 *   such as `node_modules/@scope/node_modules/`: it does not exist, so a
 *   command could create it and be loaded instead;
 * - the package's launchers in `node_modules/.bin/`, which `npx` and
 *   `npm run` start. Seatbelt denies such a name; on Linux a mount lands on
 *   what a link leads to, so a launcher can still be re-pointed there: start
 *   the library by the package's own path, or from an install outside the
 *   write paths.
 *
 * These are names read off the disk, so they travel as literal paths: `[` or
 * `*` in a directory's name is not read as a pattern.
 *
 * Nothing is denied for a copy not installed under a `node_modules` (a
 * checkout of this repository), nor where the library is compiled into an
 * application (no file on disk to protect), and what starts the library is
 * outside this: a caller's own program that loads it.
 */

type PackageManifest = {
  name?: string
  bin?: string | Record<string, string>
  dependencies?: Record<string, string>
  optionalDependencies?: Record<string, string>
}

function readManifest(dir: string): PackageManifest | undefined {
  try {
    const parsed: unknown = JSON.parse(
      fs.readFileSync(path.join(dir, 'package.json'), 'utf8'),
    )
    return typeof parsed === 'object' && parsed !== null
      ? (parsed as PackageManifest)
      : undefined
  } catch {
    return undefined
  }
}

function exists(p: string): boolean {
  try {
    fs.lstatSync(p)
    return true
  } catch {
    return false
  }
}

/**
 * Where code in `fromDir` loads `name` from: the nearest `node_modules/<name>`
 * on the way up that holds a package; `passed` is every place looked at
 * before it. Every level counts: unlike the CommonJS loader, the ES module one
 * (this package is one) looks in a `node_modules` inside a `node_modules`.
 */
function resolveDependency(
  fromDir: string,
  name: string,
): { found: string | undefined; passed: string[] } {
  const passed: string[] = []
  for (let dir = fromDir; ; dir = path.dirname(dir)) {
    const candidate = path.join(dir, 'node_modules', name)
    if (readManifest(candidate) !== undefined) {
      return { found: candidate, passed }
    }
    passed.push(candidate)
    // Not installed (optional, say): it could be put anywhere it was sought.
    if (dir === path.dirname(dir)) return { found: undefined, passed }
  }
}

/** What to deny in place of `absent`: its first component that does not
 *  exist, which must be created for anything to appear at `absent`. */
function firstMissing(absent: string): string {
  let missing = absent
  for (
    let parent = path.dirname(missing);
    parent !== missing && !exists(parent);
    parent = path.dirname(parent)
  ) {
    missing = parent
  }
  return missing
}

/** The launchers npm made for the package at `packageRoot`: one link in the
 *  `.bin` beside it for each name its manifest declares. */
function launchersOf(packageRoot: string, manifest: PackageManifest): string[] {
  const names =
    typeof manifest.bin === 'string'
      ? [path.basename(manifest.name ?? packageRoot)]
      : Object.keys(manifest.bin ?? {})
  // node_modules/<name> or node_modules/@scope/<name>
  const holder = path.basename(path.dirname(packageRoot)).startsWith('@')
    ? path.dirname(path.dirname(packageRoot))
    : path.dirname(packageRoot)
  return names
    .map(name => path.join(holder, '.bin', name))
    .filter(launcher => exists(launcher))
}

/** Bounds the walk of the dependency graph; this package's is far smaller. */
const MAX_PACKAGES = 200

/**
 * What the installed package holding `moduleFile` is loaded from, each path
 * once: package directories, places looked at first and launchers, as the top
 * of this file lists them. Empty when the package is not installed under a
 * `node_modules`, or is not on disk. `moduleFile` is two levels below the
 * package root, as is every module of `src/sandbox` and `dist/sandbox`.
 */
export function installedPackagePaths(moduleFile: string): string[] {
  const packageRoot = path.resolve(path.dirname(moduleFile), '..', '..')
  if (!packageRoot.split(path.sep).includes('node_modules')) return []
  const own = readManifest(packageRoot)
  if (own === undefined) return []

  const packages = new Set<string>([packageRoot])
  const lookedAtFirst = new Set<string>()
  const pending = [packageRoot]
  walk: for (
    let dir = pending.shift();
    dir !== undefined;
    dir = pending.shift()
  ) {
    const manifest = readManifest(dir)
    for (const name of [
      ...Object.keys(manifest?.dependencies ?? {}),
      ...Object.keys(manifest?.optionalDependencies ?? {}),
    ]) {
      if (packages.size >= MAX_PACKAGES) break walk
      const { found, passed } = resolveDependency(dir, name)
      for (const earlier of passed) lookedAtFirst.add(firstMissing(earlier))
      if (found === undefined) continue
      if (!packages.has(found)) {
        packages.add(found)
        pending.push(found)
      }
    }
  }
  // A place inside one of the packages is denied with it.
  const outsideEvery = (p: string): boolean =>
    ![...packages].some(dir => isAtOrUnder(p, dir))
  return [
    ...packages,
    ...[...lookedAtFirst].filter(outsideEvery),
    ...launchersOf(packageRoot, own),
  ]
}

// An install does not move while the process that was loaded from it runs.
let ownInstall: string[] | undefined

function thisLibrarysInstall(): string[] {
  if (ownInstall === undefined) {
    try {
      ownInstall = installedPackagePaths(fileURLToPath(import.meta.url))
    } catch {
      // No file location at all: loaded from somewhere that is not a file.
      ownInstall = []
    }
  }
  return ownInstall
}

/**
 * The write-denies a wrap adds for the library's own files: those of
 * `installPaths` (by default this copy's, see {@link installedPackagePaths})
 * at or under one of `allowedWritePaths`, judged both as spelled and as
 * resolved; the rest are read-only in the sandbox already. Where an allowed
 * write path is a pattern, containment cannot be judged and all are denied: a
 * deny on what cannot be written changes nothing. They are literal paths: see
 * `FsWriteRestrictionConfig.literalDenyWithinAllow`.
 */
export function ownFilesWriteDenies(
  allowedWritePaths: readonly string[],
  installPaths: readonly string[] = thisLibrarysInstall(),
): string[] {
  if (installPaths.length === 0) return []
  if (allowedWritePaths.some(containsGlobCharsForPlatform)) {
    return [...installPaths]
  }
  const writable = allowedWritePaths.flatMap(allowed =>
    pathSpellings(normalizePathForSandbox(allowed)).filter(form =>
      path.isAbsolute(form),
    ),
  )
  return installPaths.filter(installed =>
    pathSpellings(installed).some(form =>
      writable.some(allowed => isAtOrUnder(form, allowed)),
    ),
  )
}
