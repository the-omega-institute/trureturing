#!/usr/bin/env python3
"""Synthetic rejection and rendering contracts for continuation generators."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from selftest import prepare

HERE = Path(__file__).resolve().parent


def run(tool):
    with tempfile.TemporaryDirectory(prefix='continuation __fixture__ with space ') as tmp:
        root = Path(tmp).resolve()
        env = prepare(root)
        env['PYTHONDONTWRITEBYTECODE'] = '1'
        envelope = root/'envelope.json'
        previous = root/'previous.md'; previous.write_text('Previous Stage A rules.\n')
        mirror = root/'mirror.md'; mirror.write_text('Full mirror checklist.\n')
        out, out_mirror = root/'out.md', root/'out-mirror.md'
        conclusion = {'verdict': 'reject', 'blocking_findings': [
            {'file_line': 'D5/Sample.lean:8', 'claim': 'Synthetic claim', 'fix': 'Apply the owner.', 'owner': 'sample_owner'}],
            'not_run': ['make lean LEAN_TARGETS="D5.S1.Sample Reg.D5.S1.Sample"']}
        def invoke(args=None):
            envelope.write_text(json.dumps({'conclusion': conclusion}))
            argv = ['sample', 'r2', str(envelope), str(root/'tree'), str(previous)]
            if tool == 'mirrorfix_cont': argv += [str(mirror), str(out), str(out_mirror), '2', 'D5.S1.Sample']
            else: argv += [str(out)]
            return subprocess.run([sys.executable, str(HERE/(tool+'.py')), *(argv if args is None else args)],
                                  cwd=root/'main', env=env, capture_output=True, text=True, timeout=15)
        result = invoke()
        assert result.returncode == 0, (result.stdout, result.stderr)
        text = out.read_text()
        assert text.endswith(previous.read_text()) and 'make lean LEAN_TARGETS="D5.S1.Sample' in text
        if tool == 'mirrorfix_cont':
            assert out_mirror.read_text().endswith(mirror.read_text())
            assert 'Return `approve` or `reject`' in out_mirror.read_text()
            assert 'The `comment` verdict is forbidden' in out_mirror.read_text()
            previous = root/'rework-sample.md'; previous.write_text('Rework Stage A rules.\n')
            assert invoke().returncode == 0 and 'do not fast-forward, merge or rebase' in out.read_text()
            del conclusion['blocking_findings'][0]['fix']
        else:
            for command in ["make lean LEAN_TARGETS='D5.S1.Sample Reg.D5.S1.Sample'", 'make lean LEAN_TARGETS=D5.S1.Sample']:
                conclusion['not_run'] = [command]
                result = invoke(); assert result.returncode == 0, result.stderr
            conclusion['not_run'] = ['make lean LEAN_TARGETS="bad/module"']
        before = out.read_text()
        result = invoke()
        assert result.returncode == 13 and out.read_text() == before, result.stderr
        if tool == 'lockretry_head':
            conclusion['not_run'] = ['make lean LEAN_TARGETS="D5.S1.Sample Reg.D5.S1.Sample"']
            previous = root/'rework-sample.md'; previous.write_text('Rework Stage A rules.\n')
            result = invoke(); assert result.returncode == 0, result.stderr
            rework_text = out.read_text()
            assert 'do not fast-forward, merge or rebase `origin/dev`' in rework_text
            assert '--ff-only' not in rework_text
            previous = root/'previous.md'; previous.write_text('Previous Stage A rules.\n')
            result = invoke(); assert result.returncode == 0, result.stderr
            assert 'git merge --ff-only origin/dev' in out.read_text()
            conclusion['not_run'] = ['make lean']
            assert invoke().returncode == 13
        previous.unlink()
        assert invoke().returncode == 11
        assert invoke([]).returncode == 10
    print('CONTINUATION_SELFTEST tool=' + tool + ' failed=0')
    return 0


if __name__ == '__main__':
    for tool in (['mirrorfix_cont', 'lockretry_head'] if sys.argv[1:] in ([], ['--selftest']) else sys.argv[1:]):
        run(tool)
