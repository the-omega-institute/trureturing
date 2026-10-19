#!/usr/bin/env python3
"""Hermetic landing and main-cache loop contracts."""
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

TOOLS = Path(__file__).resolve().parents[1]
HEAD, MERGE, LATER = ('1' * 40, '2' * 40, '3' * 40)


def stub(kind, args):
    root = Path(os.environ['LAND_FIXTURE'])
    case = os.environ['LAND_CASE']
    with (root / 'commands.jsonl').open('a') as out:
        out.write(json.dumps([kind, *args]) + '\n')
    if kind == 'sleep':
        if case == 'red-poll-fail': sys.exit(36)
        return
    if kind == 'make':
        if case == 'restore-fail' and 'lean-cache-from-github-without-mathlib' in args: sys.exit(31)
        if case == 'lean-fail' and args == ['lean']: sys.exit(32)
        return
    if kind == 'git':
        if 'worktree' in args: print('worktree ' + str(root / 'main'))
        elif 'get-url' in args: print('https://github.com/example/fixture.git')
        elif args[:1] == ['branch']: print('topic' if case == 'nondev' else 'dev')
        elif args[:1] == ['status']:
            if case == 'dirty': print(' M changed')
        elif args[:1] == ['fetch']:
            if case in ('fetch-fail', 'red-fetch-fail'): sys.exit(35)
            if case == 'red-refetch-fail':
                counter = root / 'fetches'
                if counter.exists(): sys.exit(35)
                counter.touch()
        elif args[:1] == ['rev-parse']:
            if args[1].startswith('refs/remotes/pr/'):
                print(LATER if case == 'fetched-head' else HEAD)
            else: print((root / 'head').read_text())
        elif args[:1] == ['merge-tree']:
            print(MERGE)
            if case == 'conflict': sys.exit(1)
        elif args[:1] == ['ls-tree']:
            if case != 'empty-state': print('Golden/Frozen/state/D5/Sample.lean.json')
            if case == 'duplicate': print('Golden/Frozen/accepted/retired.json')
        elif args[:1] == ['merge-base']:
            expected = ([MERGE, LATER] if os.environ['LAND_MODE'] == 'land-watch' else
                        [(root/'head').read_text(), HEAD if case == 'same-head' else LATER])
            assert args == ['merge-base', '--is-ancestor', *expected], args
            if case in ('divergent', 'red-unrelated', 'red-ancestry-error'):
                sys.exit(128 if case == 'red-ancestry-error' else 1)
        elif args[:1] == ['cat-file']:
            if case == 'red-refetch-fail': sys.exit(1)
        elif args[:1] == ['merge']:
            assert args == ['merge', '--ff-only', '-q', LATER], args
            (root / 'head').write_text(LATER)
        else: raise AssertionError(('unexpected git', args))
        return
    assert kind == 'gh'
    if args[:2] == ['pr', 'view']:
        counter = root/'pr-reads'
        count = int(counter.read_text())+1 if counter.exists() else 1
        counter.write_text(str(count))
        head = LATER if case == 'head-mismatch' or (case == 'land-head-race' and count > 2) else HEAD
        state = 'CLOSED' if case == 'closed' else 'OPEN' if case.startswith('land') or case in (
            'duplicate', 'conflict', 'empty-state', 'fetched-head', 'head-mismatch', 'ci-red', 'missing-check', 'fetch-fail') else 'MERGED'
        if case == 'merge-timeout': state = 'OPEN'
        print(json.dumps({'headRefOid': head, 'body': (root / 'body.md').read_text(),
                          'state': state, 'mergeCommit': {'oid': MERGE}}))
    elif args[:2] == ['pr', 'edit']:
        (root / 'body.md').write_text(Path(args[args.index('--body-file')+1]).read_text())
    elif args[:2] == ['pr', 'checks']:
        print(json.dumps([] if case == 'missing-check' else [{'bucket': 'fail' if case == 'ci-red' else
                                                              'pending' if case == 'land-pending' else 'pass'}]))
        if case == 'land-pending': sys.exit(8)
    elif args[:2] == ['pr', 'ready']: pass
    elif args[:2] == ['pr', 'merge']:
        assert '--match-head-commit' in args and args[args.index('--match-head-commit')+1] == HEAD
        assert ('--auto' in args) == (case == 'land-pending')
    elif args[:2] == ['run', 'list']:
        if '--commit' in args:
            runs = [] if case == 'no-run' else [dict(databaseId=10, headSha=MERGE, status='completed',
                                                   conclusion='success' if case == 'own-green' else 'failure')]
        else:
            if case == 'red-list-fail': sys.exit(37)
            if case == 'red-list-json': print('{'); return
            if case == 'red-list-shape': print('{}'); return
            runs = [dict(databaseId=20, headSha=LATER, status='completed', conclusion='success')]
            if case in ('red-no-later', 'red-poll-fail'): runs = []
            if case == 'red-older': runs[0]['databaseId'] = 5
            if case == 'red-in-progress': runs[0]['status'] = 'in_progress'
            if case == 'red-list-sha': runs[0]['headSha'] = 'invalid'
            if case == 'red-list-id': runs[0]['databaseId'] = 0
            if case == 'red-list-key': del runs[0]['headSha']
        print(json.dumps(runs))
    elif args[:2] == ['run', 'watch']:
        if case == 'red-watch-timeout':
            import time
            time.sleep(3)
        if case == 'red-tool-missing': (root/'bin/gh').unlink()
        if case == 'red-tool-denied': (root/'bin/gh').chmod(0o644)
        sys.exit(0 if case == 'own-green' else 1)
    elif args[:2] == ['run', 'view']:
        if case == 'red-view-fail': sys.exit(38)
        if case == 'red-view-json': print('{'); return
        if case == 'red-view-key': print('{}'); return
        print(json.dumps({'status': 'in_progress' if case == 'red-view-incomplete' else 'completed',
                          'conclusion': 'success' if case == 'own-green' else 'failure'}))
    elif args[:1] == ['api']:
        assert '--paginate' in args and '--slurp' in args
        print(json.dumps([[]] if case == 'no-release' else [
            [{'tag_name': 'lean-cache-v2-old', 'created_at': '1'},
             {'tag_name': 'unrelated-newest', 'created_at': '3'}],
            [{'tag_name': 'lean-cache-v2-new', 'created_at': '2'}]]))
    elif args[:2] == ['release', 'download']:
        assert args[2] == 'lean-cache-v2-new'
        Path(args[args.index('--dir')+1], 'manifest.json').write_text(json.dumps(
            {'producer_commit_sha': HEAD if case == 'same-head' else 'invalid' if case == 'bad-manifest' else LATER}))
    else: raise AssertionError(('unexpected gh', args))


def fixture(root, case):
    for directory in ('main', 'tree', 'scratch', 'state', 'sshx', 'bin'):
        (root / directory).mkdir()
    target = root / 'repo/tools/scripts/agent/openproblem'
    shutil.copytree(TOOLS, target, ignore=shutil.ignore_patterns('__pycache__'))
    # Inject a clock into the copied module; production time and subprocess waits stay untouched.
    warm = target/'pipeline/main_warm.py'
    warm.rename(warm.with_name('main_warm_impl.py'))
    warm.write_text('import runpy,types,sys\nfrom pathlib import Path\n'
                    'scope=runpy.run_path(str(Path(__file__).with_name("main_warm_impl.py")))\n'
                    'ticks=iter([0,0,1,1,7200,7200])\n'
                    'scope["main"].__globals__["time"]=types.SimpleNamespace(monotonic=lambda: next(ticks))\n'
                    'sys.exit(scope["entry"](scope["main"]))\n')
    env = {k: v for k, v in os.environ.items() if not k.startswith(('OP_', 'BRIEF_', 'CHAIN_', 'LAND_'))}
    env.update(LAND_FIXTURE=str(root), LAND_CASE=case, OP_SCRATCH=str(root/'scratch'),
               OP_STATE=str(root/'state'), SSHX_HOME=str(root/'sshx'), OP_NAME_PREFIX='fixture-',
               OP_MERGE_ROUNDS='2', OP_RUN_ROUNDS='2', OP_LATER_ROUNDS='2', OP_POLL_SECONDS='0',
               OP_RUN_TIMEOUT='1', OP_REFRESH_LOCK_ROUNDS='2', PYTHONDONTWRITEBYTECODE='1', PATH=str(root/'bin')+os.pathsep+os.environ['PATH'])
    for kind in ('git', 'gh', 'make', 'sleep'):
        p = root / 'bin' / kind
        p.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' + shlex.quote(str(Path(__file__).resolve())) +
                     ' --stub ' + kind + ' "$@"\n')
        p.chmod(0o755)
    if case in ('red-tool-missing', 'red-tool-denied'):
        env['PATH'] = str(root/'bin')
        (root/'bin/python3').symlink_to(sys.executable)
        (root/'bin/dirname').symlink_to(shutil.which('dirname'))
    if case == 'lock-busy': (root/'state/main-lean.lock').mkdir()
    if case in ('xdg-lock-busy', 'home-lock-busy', 'state-overrides-xdg', 'lock-override-busy'):
        env.update(HOME=str(root/'home'), XDG_STATE_HOME=str(root/'xdg state'))
        env.pop('OP_STATE')
        lock = root/'xdg state/trureturing-op/main-lean.lock'
        if case == 'home-lock-busy':
            env.pop('XDG_STATE_HOME')
            lock = root/'home/.local/state/trureturing-op/main-lean.lock'
        elif case == 'state-overrides-xdg':
            env['OP_STATE'] = str(root/'state')
        elif case == 'lock-override-busy':
            env['OP_REFRESH_LOCK'] = str(root/'custom lock')
            lock = root/'custom lock'
        lock.parent.mkdir(parents=True, exist_ok=True)
        reader_env = dict(env)
        if case == 'state-overrides-xdg': reader_env.pop('OP_STATE')
        reader = subprocess.run(
            ['/bin/bash', '-c', '. "$1"; op_init; mkdir "$OP_REFRESH_LOCK"',
             'reader-lock', str(target/'pipeline/common.sh')],
            cwd=root, env=reader_env, text=True, capture_output=True, timeout=15)
        assert reader.returncode == 0 and lock.is_dir(), (case, reader.stdout, reader.stderr)
    if case == 'stamp-definition-moved':
        common = target/'briefgen/common.py'
        text, count = re.subn(r'(?m)^MAIN_WARM_STAMP = .*$',
                              "MAIN_WARM_STAMP = '.lake/build/moved warm stamp'", common.read_text())
        assert count == 1
        common.write_text(text)
    (root / 'head').write_text(HEAD)
    (root / 'commands.jsonl').write_text('')
    body = '| round | head | seat | carrier | decision |\n| --- | --- | --- | --- | --- |\n\nRound 1 seat layout at `' + HEAD + '`: architecture codex-cli, quality codex-cli, tests codex-cli.\n'
    (root / 'body.md').write_text(body)
    return target, env


def invoke(target, mode, args, env, root):
    return subprocess.run(['/bin/bash', str(target/'pipeline'/ (mode+'.sh')), *args], cwd=root,
                          env=dict(env, LAND_MODE=mode), text=True, capture_output=True, timeout=25)


def run(mode, only=None):
    if mode == 'land' and only is None: shared_validators()
    cases = ({'land-green': (0, 'LAND_MERGED'), 'land-pending': (0, 'LAND_AUTO'),
              'land-reject': (20, 'LAND_STANDING_REJECT'), 'head-mismatch': (14, 'LAND_HEAD_MISMATCH'),
              'fetched-head': (14, 'LAND_FETCHED_HEAD_MISMATCH'), 'land-head-race': (14, 'LAND_HEAD_MISMATCH'), 'duplicate': (21, 'LAND_DUPLICATE_FREEZE'),
              'conflict': (21, 'LAND_MERGE_CONFLICT'), 'empty-state': (24, 'LAND_NO_STATE_RECORDS'),
              'ci-red': (23, 'LAND_REQUIRED_RED_OR_MISSING'), 'missing-check': (23, 'LAND_REQUIRED_RED_OR_MISSING'),
              'fetch-fail': (16, 'command failed'), 'land-record': (0, 'LAND_RECORDED')}
             if mode == 'land' else
             {'own-green': (0, 'DEVPUSH_OK '), 'red-later': (0, 'DEVPUSH_OK_LATER'),
              'red-no-later': (1, 'DEVPUSH_RED'), 'red-unrelated': (1, 'DEVPUSH_RED'),
              'red-older': (1, 'DEVPUSH_RED'), 'red-in-progress': (1, 'DEVPUSH_RED'),
              'red-ancestry-error': (16, 'cannot check later run ancestry'),
              'red-fetch-fail': (16, 'command failed'), 'red-refetch-fail': (16, 'command failed'),
              'red-list-fail': (16, 'command failed'), 'red-list-json': (13, 'DEVPUSH_RED'),
              'red-list-shape': (13, 'run list required'), 'red-list-key': (13, 'DEVPUSH_RED'),
              'red-list-sha': (13, 'full commit SHA required'), 'red-list-id': (13, 'positive integer'),
              'red-view-fail': (16, 'command failed'), 'red-view-json': (13, 'DEVPUSH_RED'),
              'red-view-key': (13, 'DEVPUSH_RED'), 'red-view-incomplete': (124, 'DEVPUSH_TIMEOUT'),
              'red-watch-timeout': (124, 'DEVPUSH_TIMEOUT'), 'red-poll-fail': (16, 'command failed'),
              'red-tool-missing': (11, 'DEVPUSH_RED'), 'red-tool-denied': (16, 'DEVPUSH_RED'),
              'closed': (4, 'CLOSED_UNMERGED'), 'no-run': (2, 'DEVPUSH_NORUN'),
              'merge-timeout': (124, 'MERGE_WAIT_TIMEOUT')}
             if mode == 'land-watch' else
             {'advance': (0, 'MAIN_WARM_ADVANCE'), 'same-head': (0, 'MAIN_WARM_KEEP'),
              'divergent': (0, 'MAIN_WARM_KEEP'), 'dirty': (0, 'MAIN_WARM_SKIP'),
              'nondev': (0, 'MAIN_WARM_SKIP'), 'no-release': (0, 'MAIN_WARM_NO_RELEASE'),
              'bad-manifest': (13, 'full commit SHA required'), 'lock-busy': (15, 'MAIN_WARM_LOCK_FAILED'), 'restore-fail': (16, 'MAIN_WARM_RESTORE_FAILED'),
              'lean-fail': (16, 'MAIN_WARM_LEAN_FAILED'),
              'xdg-lock-busy': (15, 'MAIN_WARM_LOCK_FAILED'), 'home-lock-busy': (15, 'MAIN_WARM_LOCK_FAILED'),
              'state-overrides-xdg': (0, 'MAIN_WARM_ADVANCE'), 'lock-override-busy': (15, 'MAIN_WARM_LOCK_FAILED'),
              'stamp-definition-moved': (0, 'MAIN_WARM_ADVANCE')})
    if only: cases = {only: cases[only]}
    for case, (code, marker) in cases.items():
        with tempfile.TemporaryDirectory(prefix='landing __fixture__ with space ') as tmp:
            root = Path(tmp).resolve(); target, env = fixture(root, case)
            args = (['12345', '1', HEAD, 'approve', 'reject' if case == 'land-reject' else 'approve', 'approve'] +
                    ([] if case == 'land-record' else ['close']) if mode == 'land' else
                    ['12345', str(root/'tree')] if mode == 'land-watch' else ['2', '0.01'])
            result = invoke(target, mode, args, env, root)
            assert result.returncode == code and marker in result.stdout+result.stderr, (mode, case, result.returncode, result.stdout, result.stderr)
            commands = [json.loads(s) for s in (root/'commands.jsonl').read_text().splitlines()]
            merged = [c for c in commands if c[:3] == ['gh', 'pr', 'merge']]
            if mode == 'land':
                assert bool(merged) == (case in ('land-green', 'land-pending')), (case, commands)
                if case == 'land-reject': assert '| reject |' in (root/'body.md').read_text()
            elif mode == 'land-watch':
                removed = [c for c in commands if c[:2] == ['make', 'worktree-remove']]
                assert bool(removed) == (case in ('own-green', 'red-later')), (case, commands)
                if case == 'red-later': assert 'own_run=10 later_run=20' in result.stdout
                if case.startswith('red-') and code:
                    output = result.stdout + result.stderr
                    assert 'DEVPUSH_RED ' + MERGE + ' run=10 reason=' in result.stdout, output
                    assert not removed
            else:
                builds = [c for c in commands if c[:2] == ['make', 'lean']]
                advancing = case in ('advance', 'state-overrides-xdg', 'stamp-definition-moved')
                assert bool(builds) == (advancing or case == 'lean-fail'), (case, commands)
                assert (root/'state/main-lean.lock').exists() == (case == 'lock-busy')
                if case == 'xdg-lock-busy': assert (root/'xdg state/trureturing-op/main-lean.lock').is_dir()
                if case == 'home-lock-busy': assert (root/'home/.local/state/trureturing-op/main-lean.lock').is_dir()
                if case == 'lock-override-busy': assert (root/'custom lock').is_dir()
                if advancing:
                    assert len(builds) == 1
                    stamp = root/('main/.lake/build/moved warm stamp' if case == 'stamp-definition-moved'
                                 else 'main/.lake/build/.main-built-at')
                    assert stamp.read_text().split()[0] == LATER
                    if case == 'stamp-definition-moved': assert not (root/'main/.lake/build/.main-built-at').exists()
                    reader = subprocess.run(
                        ['/bin/bash', '-c', '. "$1"; op_data stale "$2" "$3" "10800"',
                         'stamp-reader', str(target/'pipeline/common.sh'), str(root/'main'), str(root/'tree')],
                        cwd=root, env=env, capture_output=True, text=True, timeout=15)
                    assert reader.returncode == 0 and reader.stdout.startswith('refresh ' + LATER + ' '), \
                        (reader.returncode, reader.stdout, reader.stderr)
            print('PIPELINE_CASE', mode, case, 'EXIT=' + str(result.returncode))
    with tempfile.TemporaryDirectory(prefix='landing __inputs__ with space ') as tmp:
        root = Path(tmp).resolve(); target, env = fixture(root, 'land-green')
        args = ['invalid'] if mode == 'land' else ['bad']
        result = invoke(target, mode, args, env, root)
        assert result.returncode in (10, 13), (mode, result.returncode, result.stderr)
    print('PIPELINE_SELFTEST tool=' + mode + ' failed=0')
    return 0


def shared_validators():
    sys.path[:0] = [str(TOOLS/'pipeline'), str(TOOLS/'chains'), str(TOOLS/'briefgen')]
    import common
    import landing
    import main_warm
    import runtime
    for module in (landing, main_warm, runtime):
        for validator in ('uint', 'sha'):
            assert getattr(module, validator, None) is getattr(common, validator, False), (module.__name__, validator)
    assert common.uint('12', 'test') == 12
    assert common.sha(HEAD) == HEAD
    for validator, values in ((common.uint, ('0', '-1', '1.5', '', 'x')),
                              (common.sha, ('1'*39, 'A'*40, '', None))):
        for value in values:
            try: validator(value)
            except common.BriefError as exc: assert exc.code == 13
            else: raise AssertionError(('invalid accepted', validator.__name__, value))
    print('PIPELINE_CASE shared-validators EXIT=0')
    readme = (TOOLS/'README.md').read_text()
    assert '.lake/.main-built-at' not in readme and 'MAIN_WARM_STAMP' in readme
    print('PIPELINE_CASE readme-stamp-definition EXIT=0')


if __name__ == '__main__':
    if sys.argv[1:2] == ['--stub']: stub(sys.argv[2], sys.argv[3:])
    else:
        for mode in (['land', 'land-watch', 'main-warm'] if len(sys.argv) == 1 or sys.argv[1] == '--selftest' else [sys.argv[1]]):
            run(mode)
