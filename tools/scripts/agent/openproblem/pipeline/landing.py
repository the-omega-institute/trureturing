#!/usr/bin/env python3
"""Standing, merge-result freeze checks and bounded post-merge verification."""
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS / 'briefgen'))
from common import BriefError, Context, entry, fail, sha, uint
from standing_append import checker


class Landing:
    def __init__(self):
        self.ctx = Context(required=('gh', 'make', 'sleep'))

    def run(self, *args, check=True, timeout=None):
        result = subprocess.run([str(x) for x in args], cwd=self.ctx.main,
                                text=True, capture_output=True, timeout=timeout)
        if check and result.returncode:
            fail(16, 'command failed: ' + ' '.join(map(str, args[:3])) + ': ' + result.stderr.strip())
        return result

    def gh(self, *args, **kwargs):
        return self.run('gh', *args, '-R', self.ctx.slug, **kwargs)

    def pr(self, pr):
        data = json.loads(self.gh('pr', 'view', pr, '--json', 'state,headRefOid,body,mergeCommit').stdout)
        sha(data['headRefOid'])
        return data

    def head(self, pr, reviewed):
        data = self.pr(pr)
        if data['headRefOid'] != reviewed:
            fail(14, 'LAND_HEAD_MISMATCH')
        if data['state'] != 'OPEN':
            fail(22, 'LAND_NOT_OPEN')
        return data

    def duplicate_check(self, pr, reviewed):
        self.run('git', 'fetch', '-q', 'origin', 'dev',
                 '+refs/pull/' + pr + '/head:refs/remotes/pr/' + pr)
        fetched = self.run('git', 'rev-parse', 'refs/remotes/pr/' + pr).stdout.strip()
        if fetched != reviewed:
            fail(14, 'LAND_FETCHED_HEAD_MISMATCH')
        merged = self.run('git', 'merge-tree', '--write-tree', 'origin/dev', reviewed, check=False)
        if merged.returncode:
            fail(21, 'LAND_MERGE_CONFLICT')
        tree = sha(merged.stdout.splitlines()[0])
        paths = self.run('git', 'ls-tree', '-r', '--name-only', tree, '--',
                         'Golden/Frozen/state', 'Golden/Frozen/accepted').stdout.splitlines()
        states = [p for p in paths if p.startswith('Golden/Frozen/state/') and p.endswith('.lean.json')]
        accepted = [p for p in paths if p.startswith('Golden/Frozen/accepted/')]
        print('state_records', len(states), 'accepted_files', len(accepted), flush=True)
        if accepted:
            fail(21, 'LAND_DUPLICATE_FREEZE ' + ', '.join(accepted[:20]))
        if not states:
            fail(24, 'LAND_NO_STATE_RECORDS')

    def land(self, args):
        if len(args) not in (6, 7) or (len(args) == 7 and args[-1] != 'close'):
            fail(10, 'land.sh PR ROUND HEAD ARCHITECTURE QUALITY TESTS [close]')
        pr, rnd, reviewed, *votes = args[:6]
        uint(pr, 'PR'); uint(rnd, 'round'); sha(reviewed)
        if any(v not in ('approve', 'reject', 'abstain') for v in votes):
            fail(13, 'approve, reject or abstain required')
        closed = len(args) == 7
        current = self.head(pr, reviewed)
        tally = (f'Round {rnd} tally: {votes.count("approve")} approve, {votes.count("reject")} reject, '
                 f'{votes.count("abstain")} abstain; three codex-cli verification seats; single model family. '
                 'Carried-forward approvals: none. Disagreement adjudication: ' +
                 ('the head does not clear.' if 'reject' in votes else 'none.'))
        spec = {'rows': [f'| {rnd} | `{reviewed}` | {role} | codex-cli | {vote} |'
                         for role, vote in zip(('architecture', 'quality', 'tests'), votes)],
                'tally': tally,
                'next': 'No round is open.' if closed else
                        f'Round {int(rnd)+1} seat layout at `HEAD`: architecture codex-cli, quality codex-cli, tests codex-cli; single model family.'}
        # The canonical parser owns both body editing and standing validation.
        module = checker()
        proposed = module.append_body(current['body'], reviewed, spec)
        findings = module.check(proposed, closed=closed, next_round=None if closed else int(rnd)+1)
        if findings and 'reject' not in votes:
            fail(20, 'LAND_STANDING_INVALID ' + '; '.join(findings))
        with tempfile.TemporaryDirectory(prefix='op-land __round__ ') as tmp:
            path = Path(tmp) / 'standing.json'
            path.write_text(json.dumps(spec))
            self.run(sys.executable, TOOLS / 'briefgen/standing_append.py', pr, path)
        if 'reject' in votes:
            fail(20, 'LAND_STANDING_REJECT')
        if not closed:
            print('LAND_RECORDED', pr, rnd)
            return
        current = self.head(pr, reviewed)
        findings = module.check(current['body'], closed=True)
        if findings:
            fail(20, 'LAND_STANDING_INVALID ' + '; '.join(findings))
        self.duplicate_check(pr, reviewed)
        checks = self.gh('pr', 'checks', pr, '--required', '--json', 'bucket', check=False)
        if checks.returncode not in (0, 8):
            fail(23, 'LAND_REQUIRED_RED ' + checks.stderr.strip())
        buckets = [c['bucket'] for c in json.loads(checks.stdout)]
        if not buckets or any(b not in ('pass', 'skipping', 'pending') for b in buckets):
            fail(23, 'LAND_REQUIRED_RED_OR_MISSING')
        self.head(pr, reviewed)
        self.gh('pr', 'ready', pr)
        flags = ['--auto'] if 'pending' in buckets else []
        self.gh('pr', 'merge', pr, '--merge', '--match-head-commit', reviewed, *flags)
        print('LAND_AUTO' if flags else 'LAND_MERGED', pr, reviewed)

    def pause(self, interval):
        self.run('sleep', str(interval))

    def runs(self, merge=None):
        args = ['run', 'list', '--branch', 'dev', '--event', 'push', '--workflow', 'ci-current.yml',
                '--limit', '15', '--json', 'databaseId,headSha,status,conclusion']
        if merge:
            args += ['--commit', merge]
        data = json.loads(self.gh(*args).stdout)
        if not isinstance(data, list):
            fail(13, 'run list required')
        for row in data:
            uint(row['databaseId'], 'run id'); sha(row['headSha'])
        return data

    def cleanup(self, tree):
        if tree:
            result = self.run('make', 'worktree-remove', 'NAMES=' + tree.name, check=False)
            print(result.stdout, end='')
            print('WT_REMOVE_EXIT=' + str(result.returncode), flush=True)
            if result.returncode:
                fail(16, 'WORKTREE_REMOVE_FAILED ' + result.stderr.strip())

    def devpush_red(self, merge, run_id, reason, code):
        reason = ' '.join(str(reason).split())
        print('DEVPUSH_RED', merge, 'run=' + run_id, 'reason=' + reason, flush=True)
        fail(code, reason)

    def watch(self, args):
        if len(args) not in (1, 2):
            fail(10, 'land-watch.sh PR [WORKTREE]')
        pr = args[0]; uint(pr, 'PR')
        tree = None
        if len(args) == 2:
            tree = Path(args[1])
            tree = (tree if tree.is_absolute() else self.ctx.main / tree).resolve()
            if not tree.is_dir(): fail(11, 'worktree missing')
            if tree == self.ctx.main.resolve(): fail(13, 'cannot remove main checkout')
            if re.search(r'\s', tree.name): fail(13, 'worktree basename cannot contain whitespace')
        bounds = [uint(os.environ.get(k, default), k) for k, default in
                  [('OP_MERGE_ROUNDS', '240'), ('OP_RUN_ROUNDS', '40'), ('OP_LATER_ROUNDS', '60'),
                   ('OP_RUN_TIMEOUT', '14400')]]
        interval = os.environ.get('OP_POLL_SECONDS', '60')
        if not re.fullmatch(r'(?:[0-9]+)(?:\.[0-9]+)?', interval): fail(13, 'invalid poll interval')
        merge = None
        for i in range(bounds[0]):
            current = self.pr(pr)
            if current['state'] == 'MERGED':
                merge = sha(current['mergeCommit']['oid'])
                print('MERGED', pr, merge, flush=True)
                break
            if current['state'] == 'CLOSED': fail(4, 'CLOSED_UNMERGED ' + pr)
            if current['state'] != 'OPEN': fail(13, 'invalid PR state')
            print('MERGE_WAIT', pr, i+1, flush=True)
            if i+1 < bounds[0]: self.pause(interval)
        if not merge: fail(124, 'MERGE_WAIT_TIMEOUT ' + pr)
        own = None
        for i in range(bounds[1]):
            runs = self.runs(merge)
            if runs:
                own = runs[0]
                if own['headSha'] != merge: fail(13, 'own run head mismatch')
                break
            print('DEVPUSH_WAIT', merge, i+1, flush=True)
            if i+1 < bounds[1]: self.pause(interval)
        if own is None: fail(2, 'DEVPUSH_NORUN ' + merge)
        run_id = str(own['databaseId'])
        try:
            self.verify_devpush(merge, run_id, bounds, interval)
        except BriefError as exc:
            self.devpush_red(merge, run_id, exc.message, exc.code)
        except subprocess.TimeoutExpired:
            self.devpush_red(merge, run_id, 'DEVPUSH_TIMEOUT', 124)
        except FileNotFoundError as exc:
            self.devpush_red(merge, run_id, str(exc), 11)
        except (AssertionError, ValueError, KeyError, IndexError, TypeError, AttributeError) as exc:
            self.devpush_red(merge, run_id, type(exc).__name__ + ': ' + str(exc), 13)
        except (OSError, subprocess.SubprocessError) as exc:
            self.devpush_red(merge, run_id, str(exc), 16)
        self.cleanup(tree)

    def verify_devpush(self, merge, run_id, bounds, interval):
        watched = self.gh('run', 'watch', run_id, '--exit-status', '--interval', '60',
                          check=False, timeout=bounds[3])
        status = json.loads(self.gh('run', 'view', run_id, '--json', 'status,conclusion').stdout)
        print('run', run_id, 'conclusion=' + str(status['conclusion']), 'watch_rc=' + str(watched.returncode), flush=True)
        if status['status'] != 'completed': fail(124, 'DEVPUSH_TIMEOUT ' + merge + ' run=' + run_id)
        if status['conclusion'] == 'success':
            print('DEVPUSH_OK', merge, 'run=' + run_id, flush=True)
            return
        self.run('git', 'fetch', '-q', 'origin', 'dev')
        for i in range(bounds[2]):
            for later in self.runs():
                if (int(later['databaseId']) <= int(run_id) or later['headSha'] == merge or
                        later['status'] != 'completed' or later['conclusion'] != 'success'):
                    continue
                if self.run('git', 'cat-file', '-e', later['headSha'], check=False).returncode:
                    self.run('git', 'fetch', '-q', 'origin', 'dev')
                ancestry = self.run('git', 'merge-base', '--is-ancestor', merge, later['headSha'], check=False)
                if ancestry.returncode not in (0, 1):
                    fail(16, 'cannot check later run ancestry')
                if ancestry.returncode == 0:
                    print('DEVPUSH_OK_LATER', merge, 'own_run=' + run_id,
                          'later_run=' + str(later['databaseId']), 'later_head=' + later['headSha'], flush=True)
                    return
            print('DEVPUSH_LATER_WAIT', merge, i+1, flush=True)
            if i+1 < bounds[2]: self.pause(interval)
        fail(1, 'no later successful containing run within OP_LATER_ROUNDS')


def main(argv):
    if len(argv) < 2 or argv[1] not in ('land', 'land-watch'):
        fail(10, 'landing mode required')
    if argv[2:] == ['--selftest']:
        from landing_selftest import run
        return run(argv[1])
    landing = Landing()
    return (landing.land if argv[1] == 'land' else landing.watch)(argv[2:])


if __name__ == '__main__':
    if sys.argv[1:] == ['--selftest']:
        from landing_selftest import run
        sys.exit(run('land') or run('land-watch'))
    sys.exit(entry(main, minimum=1))
