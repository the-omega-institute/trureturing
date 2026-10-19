#!/usr/bin/env python3
"""Hermetic chain contracts; optional comparison with caller-supplied source scripts."""
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS / 'briefgen'))
from selftest import prepare, stub as brief_stub


def stub(kind, args):
    root = Path(os.environ['BRIEF_FIXTURE_ROOT'])
    if kind == 'waiter':
        seat, brief, tree, stage, stagger = args
        assert Path(brief).is_file() and Path(tree).is_dir()
        assert stage in ('implementation', 'review') and stagger == '0'
        role = next((r for r in ('architecture', 'quality', 'tests') if '-'+r+'-' in seat), None)
        if role:
            preceding = {'architecture': None, 'quality': 'architecture', 'tests': 'quality'}[role]
            deadline = time.monotonic() + 0.75
            while preceding and '-'+preceding+'-' not in (root/'seats.txt').read_text():
                assert time.monotonic() < deadline, 'review launch order stalled'
                time.sleep(0.005)
        with (root / 'seats.txt').open('a') as out:
            out.write(seat + '\n')
        if role and os.environ.get('CHAIN_REQUIRE_JOIN'):
            deadline = time.monotonic() + 0.75
            while len((root/'seats.txt').read_text().splitlines()) < 3:
                assert time.monotonic() < deadline, 'reviews were not dispatched together'
                time.sleep(0.005)
        if os.environ.get('CHAIN_DISPATCH_FAIL'):
            sys.exit(37)
        verdict = ('mirror-ready' if 'continue-' in seat or re.search(r'rework-.*-r\d+$', seat)
                   else 'success' if 'implb-' in seat or re.search(r'rework-.*-r\d+b$', seat)
                   else 'approve')
        verdict = os.environ.get('CHAIN_VERDICT', verdict)
        if os.environ.get('CHAIN_REJECT_MIRROR') and 'mirror-' in seat: verdict = 'reject'
        flight = (dict(architecture='c', quality='d', tests='e')[role] if role else 'b' if 'implb-' in seat else 'a') * 24
        path = root / 'sshx' / flight / 'attempt-10/result.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        payload = {'conclusion': {'verdict': verdict, 'pr_number': 12345}}
        if os.environ.get('CHAIN_NESTED_PR') and 'implb-' in seat:
            payload['conclusion'].pop('pr_number')
            payload['conclusion']['pr'] = {'number': 12345}
        if os.environ.get('CHAIN_STATUS_ONLY') and 'implb-' in seat:
            payload['conclusion']['status'] = payload['conclusion'].pop('verdict')
        path.write_text('invalid' if os.environ.get('CHAIN_BAD_RESULT') else json.dumps(payload))
        if not os.environ.get('CHAIN_NO_RESULT'):
            if not os.environ.get('CHAIN_PRESET_ONLY') and not os.environ.get('CHAIN_PRESET_ALIAS'):
                print('FLIGHT ' + flight + ' attempt=10')
            if os.environ.get('CHAIN_PRESET_ALIAS'):
                path = root / 'sshx alias' / flight / 'attempt-10/result.json'
            print(path)
    elif kind == 'prep':
        assert len(args) == 1 and Path(args[0]).is_dir()
        (root / 'prepared').write_text(args[0])
        sys.exit(int(os.environ.get('CHAIN_PREP_FAIL', '0')))
    elif kind in ('stageb', 'head', 'postb', 'review', 'ci'):
        scratch = root / 'scratch'
        with (root / 'helpers.txt').open('a') as out: out.write(kind + '\n')
        if kind == 'stageb':
            assert args == ['sample', 'quality', 'a' * 24]
            (scratch / 'briefs/impl-op-w1-sample.stageB.filled.md').write_text('Prepared Stage B.\n')
        elif kind == 'head':
            assert args == ['sample']
            (scratch / 'briefs/implb-sample-r1.head.md').write_text('Stage B head.\n')
        elif kind in ('postb', 'review'):
            if kind == 'postb':
                assert args == ['sample', '12345']
                round_number = '1'
            else:
                assert args[0:3] == ['--codex3', 'sample', '12345']
                assert args[3] == 'lane/math/op-sample' and Path(args[4]).is_dir()
                assert Path(args[5]).is_file() and Path(args[6]).is_file()
                round_number = args[7]
            for role in ('architecture', 'quality', 'tests'):
                (scratch / ('briefs/review-sample-' + role + '-r' + round_number + '.md')).write_text('Review fixture.\n')
            if not os.environ.get('CHAIN_NO_READY'): print('READY')
        elif kind == 'ci':
            assert args == ['12345', '2' * 40]
            if os.environ.get('CHAIN_CI_FAIL'): sys.exit(38)
    elif kind == 'gh' and args[:2] == ['issue', 'view']:
        print('Preregister: Synthetic question')
    elif kind == 'gh' and args[:2] == ['pr', 'view'] and args[args.index('--json') + 1] == 'headRefOid':
        print(('1' if os.environ.get('CHAIN_UNCHANGED_HEAD') else '2') * 40)
    elif kind == 'gh' and os.environ.get('CHAIN_CI_FAIL') and args[:2] == ['run', 'view']:
        sys.exit(38)
    elif kind == 'git' and 'rev-parse' in args and '--is-bare-repository' not in args and '--show-toplevel' not in args:
        counter = root / 'head-reads'
        count = int(counter.read_text()) + 1 if counter.exists() else 1
        counter.write_text(str(count))
        print(('3' if count > 1 and os.environ.get('CHAIN_HEAD_MOVED') else '2') * 40)
    elif kind == 'git' and 'ls-remote' in args:
        print('2' * 40 + '\trefs/heads/lane/math/op-sample')
    elif kind == 'git' and 'worktree' in args:
        print('worktree ' + str(root))
    elif kind == 'sleep':
        pass
    elif kind == 'pgrep':
        sys.exit(1)
    elif kind == 'pkill':
        raise AssertionError('source attempted to stop a carrier')
    else:
        brief_stub(kind, args)


def executable(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)
    path.chmod(0o755)


def fixture(root, mode=None, integration=False):
    env = prepare(root)
    repo = root / 'repository'
    target = repo / 'tools/scripts/agent/openproblem'
    shutil.copytree(TOOLS, target, ignore=shutil.ignore_patterns('__pycache__'))
    (root / 'tools').symlink_to(repo / 'tools', target_is_directory=True)
    (root / 'sshx alias').symlink_to(root / 'sshx', target_is_directory=True)
    for kind in ('git', 'gh', 'make', 'sleep', 'pgrep', 'pkill'):
        executable(root / 'bin' / kind, '#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' +
                   shlex.quote(str(Path(__file__).resolve())) + ' --stub ' + kind + ' "$@"\n')
    for file, kind in [('pipeline/seat-wait.sh', 'waiter'), ('pipeline/prep-lane-tree.sh', 'prep')]:
        executable(target / file, '#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' +
                   shlex.quote(str(Path(__file__).resolve())) + ' --stub ' + kind + ' "$@"\n')
    if not integration:
        helpers = [('briefgen/implb_head.py', 'head'), ('briefgen/postb3.sh', 'postb'),
                   ('gen_review.py', 'review'), ('briefgen/ci_body_final.py', 'ci')]
        if mode != 'stageb-go': helpers.append(('briefgen/stageb_prep.sh', 'stageb'))
        for file, kind in helpers:
            path = target / file
            if path.suffix == '.py':
                executable(path, 'import runpy,sys\nsys.argv = [' + repr(str(Path(__file__).resolve())) +
                           ',"--stub",' + repr(kind) + '] + sys.argv[1:]\nrunpy.run_path(sys.argv[0],run_name="__main__")\n')
            else:
                executable(path, '#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' +
                           shlex.quote(str(Path(__file__).resolve())) + ' --stub ' + kind + ' "$@"\n')
    env.update(PYTHONDONTWRITEBYTECODE='1')
    lane_path = root / 'scratch/lanes/sample.json'
    lane = json.loads(lane_path.read_text())
    lane['worktree'] = 'tree'
    lane_path.write_text(json.dumps(lane))
    data = json.loads((TOOLS / 'briefgen/testdata/input.json').read_text())
    env['BRIEF_FIXTURE_BODY'] = (data['body'].replace('Round 1 seat layout', 'Round 2 seat layout') +
                                 '\n'.join(data['standing']['rows']) + '\n' + data['standing']['tally'] + '\n')
    (root / 'seats.txt').write_text('')
    for name in ('continue-sample-r1', 'mirror-sample-r1', 'mirror-check-sample-rw1', 'rework-sample-r1'):
        (root / 'scratch/briefs' / (name + '.md')).write_text('Synthetic brief.\n')
    (root / 'scratch/briefs/rework-sample-r1b.head.md').write_text(
        'Head `' + '0' * 40 + '`.\nThe independent pre-freeze mirror checked that head and approved it.\n')
    return target, env


def arguments(mode, root):
    return {
        'stagea': ['sample', str(root / 'tree'), 'continue-sample-r1', 'mirror-sample-r1'],
        'from-mirror': ['sample', str(root / 'tree'), 'mirror-sample-r1'],
        'rework': ['sample', '12345', '2', str(root / 'tree'), '1' * 40, 'r1', 'rw1'],
        'prep-and-chain': ['stagea', 'sample', str(root / 'tree'), 'continue-sample-r1', 'mirror-sample-r1'],
        'stageb-go': ['--dispatch', 'sample', 'quality', 'a' * 24],
    }[mode]


def expected(mode):
    reviews = ['fixture-review-sample-' + role + '-r' + ('2' if mode == 'rework' else '1')
               for role in ('architecture', 'quality', 'tests')]
    return {
        'stagea': ['fixture-continue-sample-r1', 'fixture-mirror-sample-r1', 'fixture-implb-sample-r1'] + reviews,
        'from-mirror': ['fixture-mirror-sample-r1', 'fixture-implb-sample-r1'] + reviews,
        'rework': ['fixture-rework-sample-r1', 'fixture-mirror-sample-rw1', 'fixture-rework-sample-r1b'] + reviews,
        'prep-and-chain': ['fixture-continue-sample-r1', 'fixture-mirror-sample-r1', 'fixture-implb-sample-r1'] + reviews,
        'stageb-go': ['fixture-implb-sample-r1'],
    }[mode]


def invoke(target, mode, root, env, args=None):
    tool = target / ('briefgen/stageb_prep.sh' if mode == 'stageb-go' else 'chains/' + mode + '.sh')
    return subprocess.run(['/bin/bash', str(tool), *(arguments(mode, root) if args is None else args)],
                          cwd=root, env=env, text=True, capture_output=True, timeout=120)


def run(mode):
    if mode == 'postb-reviews': return run_postb()
    modes = list(('stagea', 'from-mirror', 'rework', 'prep-and-chain', 'stageb-go', 'postb-reviews')) if mode == 'all' else [mode]
    for mode in modes:
        if mode == 'postb-reviews':
            run_postb()
            continue
        with tempfile.TemporaryDirectory(prefix='chain __fixture__ with spaces ') as tmp:
            root = Path(tmp).resolve()
            target, env = fixture(root, mode)
            result = invoke(target, mode, root, env)
            assert result.returncode == 0, (mode, result.stdout, result.stderr)
            seats = (root / 'seats.txt').read_text().splitlines()
            assert seats == expected(mode), (mode, seats)
            if mode == 'prep-and-chain':
                assert (root / 'prepared').read_text() == str(root / 'tree')
            print('CHAIN_SEQUENCE ' + mode + ' ' + ' -> '.join(seats))
        failures = [('CHAIN_DISPATCH_FAIL', '1', 37), ('CHAIN_BAD_RESULT', '1', 13),
                    ('CHAIN_NO_RESULT', '1', 13)] if mode != 'stageb-go' else [('CHAIN_DISPATCH_FAIL', '1', 37)]
        for key, value, code in failures:
            with tempfile.TemporaryDirectory(prefix='chain __failure__ with spaces ') as tmp:
                root = Path(tmp).resolve(); target, env = fixture(root, mode); env[key] = value
                result = invoke(target, mode, root, env)
                assert result.returncode == code, (mode, key, result.returncode, result.stdout, result.stderr)
                assert len((root / 'seats.txt').read_text().splitlines()) == 1
        if mode != 'stageb-go':
            with tempfile.TemporaryDirectory(prefix='chain __stop__ with spaces ') as tmp:
                root = Path(tmp).resolve(); target, env = fixture(root, mode); env['CHAIN_VERDICT'] = 'open'
                result = invoke(target, mode, root, env)
                assert result.returncode == 0 and 'CHAIN_STOP' in result.stdout
                assert len((root / 'seats.txt').read_text().splitlines()) == 1
        extra = ({'CHAIN_REJECT_MIRROR': (0, 2), 'CHAIN_CI_FAIL': (38, 3), 'CHAIN_NO_READY': (13, 3),
                  'CHAIN_STATUS_ONLY': (0, 6), 'CHAIN_NESTED_PR': (0, 6),
                  'CHAIN_PRESET_ONLY': (0, 6), 'CHAIN_PRESET_ALIAS': (0, 6)} if mode == 'stagea' else
                 {'CHAIN_HEAD_MOVED': (14, 2), 'CHAIN_UNCHANGED_HEAD': (0, 3), 'REWORK_SPEC': (0, 6)}
                 if mode == 'rework' else {'CHAIN_PREP_FAIL': (6, 0), 'PREP_MIRROR': (0, 5)} if mode == 'prep-and-chain' else {})
        for key, (code, count) in extra.items():
            with tempfile.TemporaryDirectory(prefix='chain __boundary__ with spaces ') as tmp:
                root = Path(tmp).resolve(); target, env = fixture(root, mode)
                args = arguments(mode, root)
                if key == 'REWORK_SPEC': args.append(str(root / 'scratch/lanes/rework-sample.json'))
                elif key == 'PREP_MIRROR': args = ['mirror', 'sample', str(root / 'tree'), 'mirror-sample-r1']
                else: env[key] = '6' if key == 'CHAIN_PREP_FAIL' else '1'
                result = invoke(target, mode, root, env, args)
                assert result.returncode == code, (mode, key, result.returncode, result.stdout, result.stderr)
                assert len((root / 'seats.txt').read_text().splitlines()) == count, (mode, key)
                if key == 'PREP_MIRROR':
                    assert (root / 'seats.txt').read_text().splitlines() == expected('from-mirror')
        with tempfile.TemporaryDirectory(prefix='chain __inputs__ with spaces ') as tmp:
            root = Path(tmp).resolve(); target, env = fixture(root, mode)
            assert invoke(target, mode, root, env, []).returncode == 10
            if mode != 'stageb-go':
                args = arguments(mode, root)
                args[1 if mode in ('stagea', 'from-mirror') else 3 if mode == 'rework' else 2] = str(root / 'absent')
                result = invoke(target, mode, root, env, args)
                assert result.returncode == 11, (mode, result.stdout, result.stderr)
                assert not (root / 'seats.txt').read_text()
        if mode == 'stagea': run_start_mirror()
        print('CHAIN_SELFTEST tool=' + mode + ' failed=0')
    return 0



def run_start_mirror():
    for rejected in (False, True):
        with tempfile.TemporaryDirectory(prefix='chain __mirror_start__ with spaces ') as tmp:
            root = Path(tmp).resolve(); target, env = fixture(root, 'stagea')
            if rejected: env['CHAIN_REJECT_MIRROR'] = '1'
            result = invoke(target, 'stagea', root, env, ['sample', str(root/'tree'), '-', 'mirror-sample-r1'])
            assert result.returncode == 0, (result.stdout, result.stderr)
            seats = (root/'seats.txt').read_text().splitlines()
            assert seats == (expected('from-mirror')[:1] if rejected else expected('from-mirror')), seats
            if not rejected: print('CHAIN_SEQUENCE stagea-minus ' + ' -> '.join(seats))


def run_postb():
    cases = [({}, 0), ({'CHAIN_DISPATCH_FAIL': '1'}, 37), ({'CHAIN_CI_FAIL': '1'}, 38),
             ({'CHAIN_NO_READY': '1'}, 13), ({'CHAIN_BAD_RESULT': '1'}, 13),
             ({'CHAIN_NO_RESULT': '1'}, 13)]
    for overrides, code in cases:
        with tempfile.TemporaryDirectory(prefix='chain __postb__ with spaces ') as tmp:
            root = Path(tmp).resolve(); target, env = fixture(root)
            env.update(CHAIN_REQUIRE_JOIN='1', **overrides)
            result = invoke(target, 'postb-reviews', root, env, ['sample', '12345', str(root/'tree')])
            assert result.returncode == code, (overrides, result.returncode, result.stdout, result.stderr)
            seats = (root/'seats.txt').read_text().splitlines()
            wanted = expected('stagea')[-3:] if not any(k in overrides for k in ('CHAIN_CI_FAIL', 'CHAIN_NO_READY')) else []
            assert seats == wanted, (overrides, seats)
            if not overrides: print('CHAIN_SEQUENCE postb-reviews ' + ' -> '.join(seats))
    print('CHAIN_SELFTEST tool=postb-reviews failed=0')
    return 0

def compare(scratch_source, shim_source=None):
    sources = {'stagea': scratch_source / 'chain-stagea-cont.sh',
               'postb-reviews': scratch_source / 'chain-postb-reviews.sh',
               'from-mirror': scratch_source / 'chain-from-mirror.sh',
               'rework': scratch_source / 'chain-rework.sh',
               'stageb-go': scratch_source / 'stageb-go.sh',
               'prep-and-chain': (shim_source / 'prep-and-chain.sh') if shim_source else Path('unused')}
    if shim_source is None:
        sources = {key: sources[key] for key in ('stagea', 'postb-reviews')}
    modes = [*sources, 'stagea-minus'] if shim_source is None else [*sources, 'prep-and-chain-mirror', 'stagea-minus']
    for mode in modes:
        source_mode = 'prep-and-chain' if mode == 'prep-and-chain-mirror' else 'stagea' if mode == 'stagea-minus' else mode
        sequences = []
        for legacy in (False, True):
            with tempfile.TemporaryDirectory(prefix='parity __fixture__ with spaces ') as tmp:
                root = Path(tmp).resolve(); target, env = fixture(root, source_mode)
                args = (['sample', str(root/'tree'), '-', 'mirror-sample-r1'] if mode == 'stagea-minus' else
                        ['sample', '12345', str(root/'tree')] if mode == 'postb-reviews' else ['mirror', 'sample', str(root / 'tree'), 'mirror-sample-r1']
                        if mode == 'prep-and-chain-mirror' else arguments(mode, root))
                if not legacy:
                    result = invoke(target, source_mode, root, env, args)
                else:
                    scratch = root / 'scratch'
                    for key, path in sources.items():
                        text = path.read_text()
                        text = re.sub(r'^S=.*$', 'S=scratch', text, flags=re.M)
                        text = re.sub(r'^cd .* \|\| exit 3$', 'cd ' + shlex.quote(str(root)) + ' || exit 3', text, flags=re.M)
                        # Only rebind source locations and the seat prefix; retain its flow.
                        match = re.search(r"grep -o '([^']+?)\[0-9a-f\]", text)
                        if match: text = text.replace(match[1], 'sshx/')
                        text = text.replace('~/.sshx/', 'sshx/')
                        match = re.search(r'dispatch-when-free.sh ([^ $]+)', text)
                        if not match: match = re.search(r'echo "([^ $]+-)implb-', text)
                        if match:
                            prefix = match[1]
                            for literal in ('rework-', 'mirror-', 'implb-', 'review-'):
                                if prefix.endswith(literal):
                                    prefix = prefix[:-len(literal)]
                                    break
                            text = text.replace(prefix, 'fixture-')
                        if key == 'prep-and-chain':
                            text = re.sub(r'W=[^;]+;', 'W=$3;', text, count=1)
                            text = text.replace('$HOME/.op-shim/prep-lane-tree.sh', '$S/prep-lane-tree.sh')
                        executable(scratch / path.name, text)
                    helpers = {'dispatch-when-free.sh': 'pipeline/seat-wait.sh',
                               'prep-lane-tree.sh': 'pipeline/prep-lane-tree.sh',
                               'stageb-prep.sh': 'briefgen/stageb_prep.sh', 'mk_stages.sh': 'briefgen/stages.sh',
                               'postb3.sh': 'briefgen/postb3.sh'}
                    for alias, actual in helpers.items():
                        executable(scratch / alias, '#!/bin/sh\nexec /bin/bash ' + shlex.quote(str(target / actual)) + ' "$@"\n')
                    for alias, actual in [('rehead.py', 'rehead.py'), ('ci-body-final.py', 'ci_body_final.py'),
                                          ('mk-implb-head-generic.py', 'implb_head.py')]:
                        executable(scratch / alias, 'import runpy,sys\nsys.path.insert(0,' + repr(str(target / 'briefgen')) +
                                   ')\nrunpy.run_path(' + repr(str(target / 'briefgen' / actual)) + ',run_name="__main__")\n')
                    executable(scratch / 'gen-review-codex3.sh', '#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' +
                               shlex.quote(str(target / 'gen_review.py')) + ' --codex3 "$@"\n')
                    executable(scratch / 'dispatch-retry.sh', '#!/bin/bash\nseat=$(tail -1 "$OP_SCRATCH/flights.txt")\nseat=${seat%% *}\nexec /bin/bash ' +
                               shlex.quote(str(target / 'pipeline/seat-wait.sh')) + ' "$seat" "$3" "$4" "$5" 0\n')
                    for block in ('lean-report-block.md', 'reuse-sweep-block.md'):
                        shutil.copyfile(target / 'templates/blocks' / block, scratch / 'briefs' / block)
                    if mode in ('stagea', 'from-mirror', 'stagea-minus'): args[1] = 'tree'
                    elif mode == 'postb-reviews': args[2] = 'tree'; env['CHAIN_REQUIRE_JOIN'] = '1'
                    elif mode == 'rework':
                        args[3] = 'tree'; args = args[:5]
                        env.update(RW='r1', MW='rw1')
                    elif source_mode == 'prep-and-chain': args[2] = 'tree'
                    elif mode == 'stageb-go': args = args[1:]
                    result = subprocess.run(['/bin/bash', str(scratch / sources[source_mode].name), *args],
                                            cwd=root, env=env, text=True, capture_output=True, timeout=120)
                assert result.returncode == 0, (mode, legacy, result.stdout, result.stderr)
                sequences.append((root / 'seats.txt').read_text().splitlines())
        wanted = expected('stagea')[-3:] if mode == 'postb-reviews' else expected('from-mirror' if mode in ('prep-and-chain-mirror', 'stagea-minus') else mode)
        assert sequences[0] == sequences[1] == wanted, (mode, sequences)
        print('CHAIN_PARITY ' + mode + ' equal=true ' + ' -> '.join(sequences[0]), flush=True)
    return 0


if __name__ == '__main__':
    if sys.argv[1:2] == ['--stub']:
        stub(sys.argv[2], sys.argv[3:])
    elif sys.argv[1:2] == ['--compare-layer3'] and len(sys.argv) == 3:
        sys.exit(compare(Path(sys.argv[2])))
    elif sys.argv[1:2] == ['--compare-scratch'] and sys.argv[3:4] == ['--shim'] and len(sys.argv) == 5:
        sys.exit(compare(Path(sys.argv[2]), Path(sys.argv[4])))
    else:
        sys.exit(run(sys.argv[1] if len(sys.argv) == 2 and sys.argv[1] != '--selftest' else 'all'))
