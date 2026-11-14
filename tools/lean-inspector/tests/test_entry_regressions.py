"""Fresh and cached reports publish without an optional FIB runtime or suite."""
import json
import os
from pathlib import Path
import subprocess
import sys
import unittest
import zipfile

import test_reuse
import publication
import reuse


class EntryRegressionTests(unittest.TestCase):
    def entry(self, *, cached=False, selected=False, regenerate=False):
        fixture = test_reuse.ReuseTests()
        fixture.setUp()
        self.addCleanup(fixture.doCleanups)
        root = fixture.root

        def write(name, text):
            path = root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(text)
            path.chmod(0o755)
            return path

        for name in ('inspect.sh', 'native.py', 'reuse.py', 'materials.py',
                     'publication.py', 'build_work.py'):
            relative = 'tools/lean-inspector/' + name
            write(relative, (test_reuse.ROOT / relative).read_text())
        # Obsolete ambient selection must not import or execute an audit.
        write('tools/lean-inspector/fib_analysis.py', 'raise AssertionError("FIB import")\n')
        write('tools/scripts/auric-fib-analysis.sh', '#!/bin/sh\nexit 98\n')
        write('bin/make', '#!/bin/sh\nexit 97\n')
        fixture.bundle()
        report = fixture.report
        reuse.seal(root, report, reuse.capture(root), publication.bundle_identity(report))
        if not cached or regenerate:
            fixture.write('D5/A.lean', 'def a := 2\n')
            fixture.report = root / 'produced' / publication.RAW
            fixture.report.parent.mkdir()
            fixture.bundle()
            with zipfile.ZipFile(root / 'produced.zip', 'w') as archive:
                for suffix in publication.SUFFIXES:
                    member = publication.member(fixture.report, suffix)
                    archive.write(member, member.name)
        write('tools/scripts/lib/resource-observation-lib.sh', 'resource_observe() { :; }\n')
        write('tools/scripts/worktree/lean-cache-ensure.sh',
              '#!/bin/sh\nprintf "ensure\\n" >> "$CALLS"\n')
        write('tools/scripts/worktree/lean-cache-run.sh', '#!/bin/sh\nexec "$@"\n')
        write('bin/lake', '#!/bin/sh\n'
              'printf "report\\n" >> "$CALLS"\nmkdir -p .lake/build/lean-inspector\n'
              'cp produced.zip .lake/build/lean-inspector/report.zip\n')
        producer = write('producer.dll', 'fixture producer')
        calls = root / 'calls'
        environment = dict(os.environ,
            PATH=os.pathsep.join((str(root / 'bin'), str(Path(sys.executable).resolve().parent), os.environ['PATH'])),
            CALLS=str(calls), LAKE_BIN=str(root / 'bin/lake'),
            STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_BUILD_TARGETS='[]',
            STRATALINT_LEAN_PRODUCER_DLL=str(producer),
            STRATALINT_FIB_REGRESSIONS_SELECTED=str(selected).lower(),
            STRATALINT_LEAN_REPORT_REUSE=str(report))
        result = subprocess.run(['bash', str(root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(root), '--output', str(report),
            '--regenerate-report-artifacts', str(int(regenerate))],
            cwd=report.parent, env=environment, capture_output=True, text=True, timeout=30)
        actual_calls = calls.read_text().splitlines() if calls.exists() else []
        return result, actual_calls, report

    def test_fresh_cached_and_regenerated_reports_need_no_fib(self):
        for cached, regenerate in ((False, False), (True, False), (True, True)):
            for selected in (False, True):
                with self.subTest(cached=cached, regenerate=regenerate, selected=selected):
                    result, calls, report = self.entry(cached=cached, regenerate=regenerate, selected=selected)
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    self.assertEqual(calls, [] if cached and not regenerate else ['ensure', 'report'])
                    self.assertNotIn('fib-regressions', result.stderr)
                    self.assertNotIn('LEAN_INSPECTOR_FIB', result.stdout + result.stderr)
                    self.assertTrue(publication.member(report, '.reuse.json').exists())
                    self.assertNotIn('fib_analysis', json.loads(report.read_text())['modules'][0])


if __name__ == '__main__':
    unittest.main()
