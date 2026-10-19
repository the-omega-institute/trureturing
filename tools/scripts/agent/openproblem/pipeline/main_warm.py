#!/usr/bin/env python3
"""Warm only a strict descendant covered by the newest cache Release."""
import json
import os
import math
import time
from datetime import datetime, timezone
from pathlib import Path
import re
import sys
import tempfile
from landing import Landing
from common import entry, fail, main_lean_lock, main_warm_stamp, sha, uint


def main(argv):
    if argv[1:] == ['--selftest']:
        from landing_selftest import run
        return run('main-warm')
    if len(argv) > 3:
        fail(10, 'main-warm.sh [HOURS [INTERVAL_SECONDS]]')
    hours = argv[1] if len(argv) > 1 else '48'
    if not re.fullmatch(r'[0-9]+(?:\.[0-9]+)?', hours): fail(13, 'invalid hours')
    duration = float(hours) * 3600
    if not math.isfinite(duration) or duration <= 0: fail(13, 'positive finite hours required')
    interval = argv[2] if len(argv) > 2 else '1800'
    if not re.fullmatch(r'[0-9]+(?:\.[0-9]+)?', interval): fail(13, 'invalid interval')
    op = Landing()
    lock = main_lean_lock()
    lock_rounds = str(uint(os.environ.get('OP_REFRESH_LOCK_ROUNDS', '480'), 'lock rounds'))
    lock.parent.mkdir(parents=True, exist_ok=True)
    deadline = time.monotonic() + duration
    while time.monotonic() < deadline:
        acquired = op.run('/bin/bash', '-c', '. "$1"; op_init; op_lock "$2" "$3"',
                          'warm-lock', Path(__file__).with_name('common.sh'), lock, lock_rounds, check=False)
        if acquired.returncode: fail(15, 'MAIN_WARM_LOCK_FAILED ' + acquired.stderr.strip())
        try:
            if (op.run('git', 'branch', '--show-current').stdout.strip() != 'dev' or
                    op.run('git', 'status', '--porcelain').stdout.strip()):
                print('MAIN_WARM_SKIP not a clean dev checkout', flush=True)
            else:
                op.run('git', 'fetch', '-q', 'origin', 'dev')
                pages = json.loads(op.run('gh', 'api', 'repos/' + op.ctx.slug + '/releases?per_page=100',
                                              '--paginate', '--slurp').stdout)
                releases = [r for page in pages for r in page if r['tag_name'].startswith('lean-cache-v2-')]
                releases.sort(key=lambda r: r['created_at'], reverse=True)
                if releases:
                    tag = releases[0]['tag_name']
                    if not re.fullmatch(r'lean-cache-v2-[A-Za-z0-9._-]+', tag): fail(13, 'invalid cache tag')
                    with tempfile.TemporaryDirectory(prefix='op-warm __manifest__ ') as tmp:
                        op.gh('release', 'download', tag, '--pattern', 'manifest.json', '--dir', tmp)
                        producer = sha(json.loads((Path(tmp) / 'manifest.json').read_text())['producer_commit_sha'])
                    head = sha(op.run('git', 'rev-parse', 'HEAD').stdout.strip())
                    if op.run('git', 'cat-file', '-e', producer, check=False).returncode:
                        op.run('git', 'fetch', '-q', 'origin', producer)
                    ancestry = op.run('git', 'merge-base', '--is-ancestor', head, producer, check=False)
                    if ancestry.returncode not in (0, 1): fail(16, 'cannot check cache producer ancestry')
                    if head != producer and ancestry.returncode == 0:
                        # Recheck immediately before mutating the main checkout.
                        if (op.run('git', 'branch', '--show-current').stdout.strip() != 'dev' or
                                op.run('git', 'status', '--porcelain').stdout.strip() or
                                op.run('git', 'rev-parse', 'HEAD').stdout.strip() != head):
                            fail(14, 'MAIN_WARM_CHECKOUT_CHANGED')
                        op.run('git', 'merge', '--ff-only', '-q', producer)
                        print('MAIN_WARM_ADVANCE', head, producer, tag, flush=True)
                        for label, command in [('RESTORE', ['make', 'lean-cache-from-github-without-mathlib', 'REFRESH_STALE=1']),
                                               ('LEAN', ['make', 'lean'])]:
                            op.ctx.state.mkdir(parents=True, exist_ok=True)
                            with (op.ctx.state / ('main-warm-' + label.lower() + '.log')).open('w') as out:
                                import subprocess
                                result = subprocess.run(command, cwd=op.ctx.main, stdout=out, stderr=subprocess.STDOUT)
                            print('MAIN_WARM_' + label + '_EXIT=' + str(result.returncode), flush=True)
                            if result.returncode: fail(16, 'MAIN_WARM_' + label + '_FAILED')
                        built = main_warm_stamp(op.ctx.main)
                        built.parent.mkdir(parents=True, exist_ok=True)
                        built.write_text(producer + ' ' + datetime.now(timezone.utc).isoformat().replace('+00:00', 'Z') + '\n')
                    else:
                        print('MAIN_WARM_KEEP', head, producer, flush=True)
                else:
                    print('MAIN_WARM_NO_RELEASE', flush=True)
        finally:
            lock.rmdir()
        remaining = deadline - time.monotonic()
        if remaining > 0: op.pause(min(float(interval), remaining))
    print('MAIN_WARM_LOOP_END', flush=True)


if __name__ == '__main__':
    sys.exit(main(sys.argv) if sys.argv[1:] == ['--selftest'] else entry(main))
