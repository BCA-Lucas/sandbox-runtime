import { afterAll, beforeAll, describe, expect, it } from 'bun:test'
import { spawnSync } from 'node:child_process'
import { mkdtempSync, realpathSync, rmSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { join } from 'node:path'
import {
  cleanupBwrapMountPoints,
  wrapCommandWithSandboxLinux,
} from '../../src/sandbox/linux-sandbox-utils.js'
import { isLinux } from '../helpers/platform.js'
import { bwrapCanNamespaceNetwork } from '../helpers/bwrap-namespace.js'

const has = (program: string): boolean =>
  spawnSync('which', [program]).status === 0

/**
 * The two relays inside the sandbox are started in the background. Here a
 * stand-in for socat starts them late, not at all, or without ever listening,
 * and the command's first action is to connect to both ports.
 */
describe.if(isLinux && bwrapCanNamespaceNetwork() && has('socat'))(
  'the relays listen before the command starts',
  () => {
    let dir: string
    let connectFirst: string

    beforeAll(() => {
      dir = realpathSync(mkdtempSync(join(tmpdir(), 'relays-listen-')))
      for (const socket of ['http.sock', 'socks.sock']) {
        writeFileSync(join(dir, socket), '')
      }
      connectFirst = join(dir, 'connect-first.sh')
      writeFileSync(
        connectFirst,
        'for p in 3128 1080; do\n' +
          '  (exec 3<>/dev/tcp/127.0.0.1/$p) 2>/dev/null && echo "$p up" || echo "$p refused"\n' +
          'done\n',
      )
    })

    afterAll(() => {
      cleanupBwrapMountPoints({ force: true })
      rmSync(dir, { recursive: true, force: true })
    })

    /** Runs `command` wrapped, with `script` standing in for socat. */
    async function run(
      script: string,
      {
        binShell = 'bash',
        command = `bash ${connectFirst}`,
        ...rest
      }: {
        binShell?: string
        command?: string
        allowAllUnixSockets?: boolean
      } = {},
    ): Promise<{ lines: string[]; ms: number }> {
      const socatPath = join(dir, 'socat-stand-in')
      writeFileSync(socatPath, `#!/bin/sh\n${script}\n`, { mode: 0o755 })
      const wrapped = await wrapCommandWithSandboxLinux({
        command,
        needsNetworkRestriction: true,
        httpSocketPath: join(dir, 'http.sock'),
        socksSocketPath: join(dir, 'socks.sock'),
        readConfig: { denyOnly: [] },
        writeConfig: { allowOnly: [dir], denyWithinAllow: [] },
        socatPath,
        binShell,
        ...rest,
      })
      const started = performance.now()
      const result = spawnSync(wrapped, {
        shell: true,
        encoding: 'utf8',
        timeout: 30000,
      })
      expect(result.stderr ?? '').not.toContain('bwrap:')
      return {
        lines: result.stdout.trim().split('\n'),
        ms: performance.now() - started,
      }
    }

    const late = 'sleep 0.3\nexec socat "$@"'
    const shells = ['bash', 'sh', 'zsh'].filter(has)
    for (const binShell of shells) {
      it(`finds both relays listening when they start late, under ${binShell}`, async () => {
        expect((await run(late, { binShell })).lines).toEqual([
          '3128 up',
          '1080 up',
        ])
      })
    }

    for (const port of [3128, 1080]) {
      it(`waits for the relay on ${port} when it is the later one`, async () => {
        const later = `case "$1" in *:${port},*) sleep 0.4 ;; esac\nexec socat "$@"`
        expect((await run(later)).lines).toEqual(['3128 up', '1080 up'])
      })
    }

    it('runs out of patience only with a relay that is there and never listens', async () => {
      const stuck = await run('exec sleep 30')
      expect(stuck.lines).toEqual(['3128 refused', '1080 refused'])
      expect(stuck.ms).toBeLessThan(15000)
      // One that has exited is not waited for.
      const exited = await run('exit 1')
      expect(exited.lines).toEqual(['3128 refused', '1080 refused'])
      expect(stuck.ms - exited.ms).toBeGreaterThan(1000)
      // And the wait ends when both listen, which every shell has to see.
      for (const binShell of shells) {
        const listening = await run(late, { binShell })
        expect(stuck.ms - listening.ms).toBeGreaterThan(1000)
      }
    }, 30000)

    it('leaves no variable of its own to a command run in the same shell', async () => {
      // Without the seccomp helper the command is evaluated by the shell
      // that waited.
      const { lines } = await run(late, {
        command: `set | grep -c '^_srt_'; bash ${connectFirst}`,
        allowAllUnixSockets: true,
      })
      expect(lines).toEqual(['0', '3128 up', '1080 up'])
    })
  },
)
