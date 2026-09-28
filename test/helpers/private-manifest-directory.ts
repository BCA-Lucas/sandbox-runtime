import { afterAll, beforeAll } from 'bun:test'
import { mkdirSync, mkdtempSync, realpathSync, rmSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import { forgetMountPointManifestDirectory } from '../../src/sandbox/bwrap-mount-manifests.js'
import { cleanupBwrapMountPoints } from '../../src/sandbox/linux-sandbox-utils.js'

/**
 * Gives the enclosing `describe` a runtime directory and a temp dir of its own,
 * for as long as its tests run.
 *
 * The manifests of every srt process of a user live in one directory, and a
 * collect reads, judges and removes all of them, so a test that lists or
 * attacks that directory would otherwise act on whatever else the user is
 * running. The library looks under `$XDG_RUNTIME_DIR` first, and every wrap
 * that restricts writes makes the directory under the temp dir as well, so both
 * are replaced, before anything is cleaned up: nothing is made or removed in
 * the directories the user's own processes keep.
 *
 * It also starts the `describe` with no wrap of this process outstanding, and
 * leaves it so: the library's count of wraps is shared by every test file of a
 * run, and other suites wrap without cleaning up.
 *
 * Call it inside the `describe` callback. Returns where the manifests go.
 */
export function usePrivateManifestDirectory(): { manifestDir(): string } {
  const replaced = ['XDG_RUNTIME_DIR', 'TMPDIR'] as const
  const saved = replaced.map(name => process.env[name])
  let base: string | undefined

  beforeAll(() => {
    base = realpathSync(mkdtempSync(join(tmpdir(), 'srt-test-')))
    for (const name of replaced) {
      process.env[name] = join(base, name)
      mkdirSync(process.env[name], { mode: 0o700 })
    }
    forgetMountPointManifestDirectory()
    cleanupBwrapMountPoints({ force: true })
  })

  afterAll(() => {
    cleanupBwrapMountPoints({ force: true })
    replaced.forEach((name, i) => {
      if (saved[i] === undefined) delete process.env[name]
      else process.env[name] = saved[i]
    })
    forgetMountPointManifestDirectory()
    if (base !== undefined) {
      rmSync(base, { recursive: true, force: true })
    }
  })

  return {
    manifestDir: () => {
      if (base === undefined) {
        throw new Error('asked for before the tests began')
      }
      return join(base, 'XDG_RUNTIME_DIR', 'srt-mount-points')
    },
  }
}
