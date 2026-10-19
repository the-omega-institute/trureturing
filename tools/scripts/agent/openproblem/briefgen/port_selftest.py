#!/usr/bin/env python3
"""Synthetic contracts for probe lane generation and preregistration filing."""
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
from selftest import prepare, stub as brief_stub

HERE = Path(__file__).resolve().parent


def stub(kind, args):
    root = Path(os.environ['BRIEF_FIXTURE_ROOT'])
    if kind == 'gh' and args[:2] == ['issue', 'view']:
        print('Preregister: Synthetic question')
    elif kind == 'gh' and args[:2] == ['issue', 'list']:
        if os.environ.get('PREREG_SEARCH_FAIL'): sys.exit(41)
        print(json.dumps([{'title': 'Synthetic question', 'number': 6}]
                         if os.environ.get('PREREG_DUPLICATE') else []))
    elif kind == 'gh' and args[:2] == ['issue', 'create']:
        if os.environ.get('PREREG_CREATE_FAIL'): sys.exit(42)
        if os.environ.get('PREREG_SECOND_FAIL') and (root / 'filed.txt').exists(): sys.exit(42)
        body = Path(args[args.index('--body-file') + 1]).read_text()
        with (root / 'filed.txt').open('a') as out: out.write(body + '\n')
        print('https://github.com/example/fixture/issues/12345')
    else:
        brief_stub(kind, args)


def fixture(root):
    env = prepare(root)
    for kind in ('git', 'gh', 'make'):
        path = root / 'bin' / kind
        path.write_text('#!/bin/sh\nexec ' + shlex.quote(sys.executable) + ' ' +
                        shlex.quote(str(Path(__file__).resolve())) + ' --stub ' + kind + ' "$@"\n')
        path.chmod(0o755)
    pending = root / 'pending'; (pending / 'post').mkdir(parents=True)
    (pending / 'post/titles.tsv').write_text('prereg-draft.md\tSynthetic question\n')
    (pending / 'prereg-draft.md').write_text('Synthetic statement with `result` and proof.\n```lean\nexample : True := trivial\n```\n')
    env.update(OP_PENDING=str(pending), PYTHONDONTWRITEBYTECODE='1')
    probe = {'conclusion': {'module_plan': [{'module': 'D5/S1/Fixtures/Sample'}],
                            'triage': [], 'scratch_files': [{'path': str(root / 'proof.lean'), 'role': 'proof'}]}}
    (root / 'sshx' / ('a' * 24) / 'attempt-1/result.json').write_text(json.dumps(probe))
    return env


def invoke(tool, root, env, args=None):
    if args is None:
        args = (['sample:draft'] if tool == 'file_prereg' else
                ['sample', '12345', 'Proved', 'D5/S1/Fixtures/Sample', str(root / 'tree'),
                 'a' * 24, 'sample', 'formalize: synthetic fixture'])
    return subprocess.run([sys.executable, str(HERE / (tool + '.py')), *args], cwd=root,
                          env=env, capture_output=True, text=True, timeout=10)


def run(tool):
    with tempfile.TemporaryDirectory(prefix='port __fixture__ with spaces ') as tmp:
        root = Path(tmp); env = fixture(root)
        result = invoke(tool, root, env)
        assert result.returncode == 0, (result.stdout, result.stderr)
        if tool == 'file_prereg':
            mapping = root / 'pending/post/issues.tsv'
            assert mapping.read_text() == 'sample\t12345\n'
            assert (root / 'filed.txt').is_file()
            filed = (root / 'filed.txt').read_text()
            assert invoke(tool, root, env).returncode == 0
            assert (root / 'filed.txt').read_text() == filed
        else:
            data = json.loads((root / 'scratch/lanes/sample.json').read_text())
            assert data['gid'] == 'D5/S1/Fixtures/Sample.result'
            assert data['branch'] == 'lane/math/op-sample'
            assert data['target_md'] == (root / 'scratch/lanes/sample.target.md').read_text()
            assert 'Synthetic question' in data['title'] and 'Problems/sample.md' in data['target_md']
            assert str(root / 'proof.lean') in data['target_md']
            assert ('Re-pin it, and run the binding "Frozen importers of published owners" block. '
                    'Each published owner `theorem`/`lemma` is a new public theorem for the §3.9 '
                    'escape audit: attempt its Reg registration, or list it by full name in the '
                    'unfinished-audit issue and name it in the PR body.') in data['target_md']
    cases = ([('LEAN_BLOCK', 13), ('COMPILE_LINE', 13), ('SHA_', 13), ('``', 13), ('`  `', 13),
              ('duplicate', 14), ('missing-draft', 11), ('missing-title', 11),
              ('search-fail', 16), ('create-fail', 16), ('invalid-map', 13), ('lock', 14),
              ('batch-missing', 11)] if tool == 'file_prereg' else
             [('missing-result', 11), ('bad-envelope', 13), ('bad-module', 13), ('bad-settlement', 13),
              ('missing-tree', 11), ('bad-key', 13)])
    for label, code in cases:
        with tempfile.TemporaryDirectory(prefix='port __reject__ with spaces ') as tmp:
            root = Path(tmp); env = fixture(root); args = None
            if tool == 'file_prereg':
                body = root / 'pending/prereg-draft.md'
                if label in ('LEAN_BLOCK', 'COMPILE_LINE', 'SHA_', '``', '`  `'): body.write_text(label)
                elif label == 'duplicate': env['PREREG_DUPLICATE'] = '1'
                elif label == 'missing-draft': body.unlink()
                elif label == 'missing-title': (root / 'pending/post/titles.tsv').write_text('')
                elif label == 'search-fail': env['PREREG_SEARCH_FAIL'] = '1'
                elif label == 'create-fail': env['PREREG_CREATE_FAIL'] = '1'
                elif label == 'invalid-map': (root / 'pending/post/issues.tsv').write_text('sample\tbad\n')
                elif label == 'lock': (root / 'pending/post/issues.lock').mkdir()
                elif label == 'batch-missing': args = ['sample:draft', 'other:absent']
            else:
                args = ['sample', '12345', 'Proved', 'D5/S1/Fixtures/Sample', str(root / 'tree'), 'a' * 24, 'sample', 'fixture']
                envelope = root / 'sshx' / ('a' * 24) / 'attempt-1/result.json'
                if label == 'missing-result': envelope.unlink()
                elif label == 'bad-envelope': envelope.write_text('{"conclusion":{}}')
                elif label == 'bad-module': args[3] = '../Sample'
                elif label == 'bad-settlement': args[2] = 'maybe'
                elif label == 'missing-tree': args[4] = str(root / 'absent')
                elif label == 'bad-key': args[0] = '../sample'
            result = invoke(tool, root, env, args)
            assert result.returncode == code, (tool, label, result.returncode, result.stdout, result.stderr)
            assert not (root / 'filed.txt').exists(), label
            print('PORT_REJECT ' + tool + ' ' + label + ' exit=' + str(code))
    if tool == 'file_prereg':
        with tempfile.TemporaryDirectory(prefix='port __partial__ with spaces ') as tmp:
            root = Path(tmp); env = fixture(root)
            (root / 'pending/post/issues.tsv').write_text('existing\t7\n')
            with (root / 'pending/post/titles.tsv').open('a') as out:
                out.write('prereg-other.md\tOther synthetic question\n')
            (root / 'pending/prereg-other.md').write_text('Other valid body.')
            env['PREREG_SECOND_FAIL'] = '1'
            result = invoke(tool, root, env, ['sample:draft', 'other:other'])
            assert result.returncode == 16, (result.stdout, result.stderr)
            assert (root / 'pending/post/issues.tsv').read_text() == 'existing\t7\nsample\t12345\n'
            assert not (root / 'pending/post/issues.lock').exists()
        print('PORT_PARTIAL file_prereg preserved=true exit=16')
    print('PORT_SELFTEST tool=' + tool + ' failed=0')
    return 0


if __name__ == '__main__':
    if sys.argv[1:2] == ['--stub']:
        stub(sys.argv[2], sys.argv[3:])
    else:
        sys.exit((run('lane_from_probe') or run('file_prereg')) if sys.argv[1:] == ['--selftest'] else run(sys.argv[1]))
