"""Production regression decisions survive phase capture without extra FIB work."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
import zipfile

import test_reuse
import fib_analysis
import materials
import publication
import reuse


class EntryRegressionTests(unittest.TestCase):
    def entry(self, *, cached=False, changed=False, selected=False, failure=0,
              unavailable_clock=False, missing_inputs=False, regenerate=False, obsolete=False, invalid_fresh=False,
              force_without_seed=None, follow_with_unchecked_report=False, legacy=False):
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
                     'publication.py', 'fib_analysis.py', 'build_work.py', 'build_inputs.py'):
            relative = 'tools/lean-inspector/' + name
            write(relative, (test_reuse.ROOT / relative).read_text())

        def bundle(identity, missing=False):
            fixture.bundle()
            value = json.loads(fixture.report.read_text())
            row = value['modules'][0]
            leaf = dict(application='D5.A.application', owner='D5.A', target='D5.A.a',
                target_module='D5.A', target_type_identity='c' * 64, input_identity=identity,
                request=dict(kind='unavailable', parameter=None), unavailable_reason='fixture',
                reading=fib_analysis.unavailable('fixture'))
            if not missing:
                row['fib_analysis'] = dict(applications=[leaf])
            fixture.report.write_bytes(materials.canonical_json(value))
            origins = json.loads(publication.member(fixture.report, '.provenance.json').read_text())['module_origins']
            origins['D5.A']['input_projection']['inputs'] = [dict(owner='D5.A',
                name=leaf['application'], type='LeanInformationAudit.AuricFib.Contract.Application')]
            origins['D5.A']['report_sha256'] = hashlib.sha256(materials.canonical_json(
                dict(schema=materials.REPORT_SCHEMA, modules=[row]))).hexdigest()
            publication.write_sidecars(fixture.report, publication.coordinates(root), origins)

        bundle('a' * 64)
        report = fixture.report
        reuse._seal(root, report, reuse.capture(root), publication.bundle_identity(report), checked=True)
        if legacy:
            reuse.write_receipt(report, reuse.capture(root))
        if obsolete:
            value = json.loads(report.read_text())
            value['modules'][0]['fib_analysis']['schema_version'] = 1
            report.write_bytes(materials.canonical_json(value))
            origins = json.loads(publication.member(report, '.provenance.json').read_text())['module_origins']
            origins['D5.A']['report_sha256'] = hashlib.sha256(materials.canonical_json(value)).hexdigest()
            publication.write_sidecars(report, publication.coordinates(root), origins)
        before = {suffix: publication.member(report, suffix).read_bytes() for suffix in publication.SUFFIXES}
        if not cached:
            fixture.write('D5/A.lean', 'def a := 2\n')
            fixture.report = root / 'produced' / publication.RAW
            fixture.report.parent.mkdir()
            bundle(('b' if changed else 'a') * 64, missing_inputs)
            if invalid_fresh:
                value = json.loads(fixture.report.read_text())
                value['modules'][0]['fib_analysis']['schema_version'] = 1
                fixture.report.write_bytes(materials.canonical_json(value))
                origins = json.loads(publication.member(fixture.report, '.provenance.json').read_text())['module_origins']
                origins['D5.A']['report_sha256'] = hashlib.sha256(materials.canonical_json(value)).hexdigest()
                publication.write_sidecars(fixture.report, publication.coordinates(root), origins)
            with zipfile.ZipFile(root / 'produced.zip', 'w') as archive:
                for suffix in publication.SUFFIXES:
                    member = publication.member(fixture.report, suffix)
                    archive.write(member, member.name)
        elif not selected and not legacy:
            # Accepted reuse must not decode the complete report for telemetry,
            # invoke the regression consumer, or launch an analyzer.
            with (root / 'tools/lean-inspector/publication.py').open('a') as script:
                script.write('\ndef report_rows(*args, **kwargs):\n'
                             '    raise AssertionError("unexpected complete row reread")\n')
            path = root / 'tools/lean-inspector/fib_analysis.py'
            path.write_text('if __name__ == "__main__":\n    raise SystemExit(96)\n' + path.read_text())

        write('tools/scripts/lib/resource-observation-lib.sh', 'resource_observe() { :; }\n')
        write('tools/scripts/worktree/lean-cache-ensure.sh',
              '#!/bin/sh\nprintf "ensure\\n" >> "$CALLS"\n')
        write('bin/dotnet', '#!/bin/sh\n[ "$2" = lean-utility-input ] || exit 74\nprintf "[]\\n"\n')
        write('tools/scripts/worktree/lean-cache-run.sh', '#!/bin/sh\n[ "$1" = --build-report-modules ] && exit 0\n[ "$1" = --prebuilt ] && shift\nexec "$@"\n')
        write('bin/lake', '#!/bin/sh\n'
              'if [ "${1:-}" = --version ]; then printf "fixture lake 1\\n"; exit 0; fi\n'
              'printf "report\\n" >> "$CALLS"\nmkdir -p .lake/build/lean-inspector\n'
              'cp produced.zip .lake/build/lean-inspector/report.zip\n')
        write('bin/make', """#!/bin/bash
case "$1" in
  lean)
    echo compile >> "$CALLS"
    echo "Build completed successfully (1 job)."
    exit 0 ;;
  lean-report)
    exec bash "$PWD/tools/lean-inspector/inspect.sh" --repository "$PWD" \
      --output "${3#LEAN_REPORT=}" --log-dir "$STRATALINT_LEAN_REPORT_LOG_DIR" \
      --regenerate-report-artifacts "$REGENERATE_REPORT_ARTIFACTS" ;;
esac
[[ "$#" == 3 && "$1" == -C && "$2" == "$PWD" && "$3" == compiled-fib-test ]] || exit 97
echo regressions >> "$CALLS"
exit """ + str(failure) + '\n')
        write('tools/scripts/auric-fib-analysis.sh', '#!/bin/sh\n'
              'printf "unexpected analyzer\\n" >> "$CALLS"\nexit 98\n')
        producer = write('producer.dll', 'fixture producer')
        shell_environment = write('shell-env', 'unset SECONDS\n' if unavailable_clock else '')
        calls = root / 'calls'
        logs = root / 'logs'
        environment = dict(os.environ, FULL_BUILD="1",
            PATH=os.pathsep.join((str(root / 'bin'), str(Path(sys.executable).resolve().parent), os.environ['PATH'])),
            CALLS=str(calls), LAKE_BIN=str(root / 'bin/lake'),
            STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_BUILD_TARGETS='[]',
            STRATALINT_LEAN_PRODUCER_DLL=str(producer),
            STRATALINT_FIB_REGRESSIONS_SELECTED=str(selected).lower(),
            STRATALINT_LEAN_REPORT_REUSE=str(report), BASH_ENV=str(shell_environment))
        environment.update(REGENERATE_REPORT_ARTIFACTS=str(int(regenerate)), STRATALINT_LEAN_REPORT_LOG_DIR=str(logs))
        if force_without_seed:
            for suffix in (*publication.SUFFIXES, reuse.SUFFIX):
                publication.member(report, suffix).unlink()
            command = [shutil.which('make'), '-f', str(test_reuse.ROOT / 'Makefile'), 'check-lean-report',
                       'FULL_BUILD=1', 'LEAN_REPORT_CACHE_MISS_POLICY=fetch-or-fail',
                       force_without_seed + '=1', 'LEAN_REPORT=' + str(report)]
        else:
            command = [sys.executable, '-B', str(root / 'tools/lean-inspector/build_inputs.py'),
                       'check', '--output', str(report)]
        result = subprocess.run(command, cwd=root, env=environment,
            capture_output=True, text=True, timeout=30)
        if follow_with_unchecked_report:
            self.assertEqual(result.returncode, failure, result.stdout + result.stderr)
            analyzed = subprocess.run(['make', 'lean-report', 'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build',
                                       'LEAN_REPORT=' + str(report)], cwd=root, env=environment,
                                      capture_output=True, text=True, timeout=30)
            self.assertEqual(analyzed.returncode, 0, analyzed.stdout + analyzed.stderr)
            self.assertEqual(reuse.read_receipt(report)['completed'], reuse.COMPLETED)
            result = subprocess.run(command, cwd=root, env=environment,
                                    capture_output=True, text=True, timeout=30)
        actual_calls = calls.read_text().splitlines() if calls.exists() else []
        return result, actual_calls, report, logs, before

    def test_analysis_publication_cannot_clear_failed_regressions(self):
        result, calls, report, _, _ = self.entry(changed=True, failure=41, follow_with_unchecked_report=True)
        self.assertEqual(result.returncode, 41, result.stdout + result.stderr)
        self.assertEqual(calls, ['compile', 'report', 'regressions', 'report', 'regressions'])
        self.assertEqual(reuse.read_receipt(report)['completed'], reuse.COMPLETED)

    def test_old_reuse_receipt_is_checked_before_becoming_a_regression_baseline(self):
        result, calls, report, _, _ = self.entry(cached=True, legacy=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['regressions'])
        self.assertEqual(reuse.read_receipt(report)['completed'], reuse.CHECKED)

    def test_explicit_recovery_without_seed_through_checked_make_entry(self):
        for option in ('REBUILD_REPORT_CACHE', 'REGENERATE_REPORT_ARTIFACTS'):
            with self.subTest(option=option):
                result, calls, report, _, _ = self.entry(force_without_seed=option)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(calls, ['compile', 'report', 'regressions'])
                self.assertTrue(publication.member(report, reuse.SUFFIX).is_file())

    def test_fresh_or_regenerated_inputs_select_the_suite_once(self):
        for regenerate, obsolete, changed, selected in (
                (False, False, False, False), (False, False, True, True),
                (True, False, True, False), (True, False, False, True),
                (True, True, False, False)):
            with self.subTest(regenerate=regenerate, changed=changed, selected=selected, obsolete=obsolete):
                result, calls, report, _, _ = self.entry(regenerate=regenerate, obsolete=obsolete,
                    changed=changed, selected=selected)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(calls, ['compile', 'report']
                                 + (['regressions'] if changed or selected or obsolete else []))
                self.assertTrue(publication.member(report, '.reuse.json').is_file())

    def test_accepted_reuse_skips_analysis_and_unselected_regressions(self):
        for selected in (False, True):
            with self.subTest(selected=selected):
                result, calls, report, _, before = self.entry(cached=True, selected=selected)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(calls, ['regressions'] if selected else [])
                self.assertEqual(report.read_bytes(), before[''])
                self.assertTrue(publication.member(report, '.reuse.json').is_file())

    def test_rejected_comparison_or_regressions_preserve_all_published_members(self):
        for options, failure in (
                (dict(changed=True, failure=41), 41),
                (dict(cached=True, selected=True, failure=41), 41),
                (dict(changed=True, missing_inputs=True), 1),
                (dict(obsolete=True), 1),
                (dict(regenerate=True, obsolete=True, invalid_fresh=True), 1)):
            with self.subTest(options=options):
                result, calls, report, _, before = self.entry(**options)
                self.assertEqual(result.returncode, failure, result.stdout + result.stderr)
                self.assertEqual(calls.count('regressions'), int(failure == 41))
                self.assertEqual(before, {suffix: publication.member(report, suffix).read_bytes()
                                          for suffix in publication.SUFFIXES})


if __name__ == '__main__':
    unittest.main()
