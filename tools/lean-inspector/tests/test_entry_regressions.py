"""Production regression decisions survive phase capture without extra FIB work."""
import hashlib
import json
import os
from pathlib import Path
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
              unavailable_clock=False, missing_inputs=False, regenerate=False, obsolete=False, invalid_fresh=False):
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
                     'publication.py', 'fib_analysis.py', 'build_work.py'):
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
        reuse.seal(root, report, reuse.capture(root), publication.bundle_identity(report))
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
        elif not selected:
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
        write('tools/scripts/worktree/lean-cache-run.sh', '#!/bin/sh\nexec "$@"\n')
        write('bin/lake', '#!/bin/sh\n'
              'if [ "${1:-}" = --version ]; then printf "fixture lake 1\\n"; exit 0; fi\n'
              'printf "report\\n" >> "$CALLS"\nmkdir -p .lake/build/lean-inspector\n'
              'cp produced.zip .lake/build/lean-inspector/report.zip\n')
        write('bin/make', '#!/bin/sh\n'
              '[ "$#" -eq 3 ] && [ "$1" = -C ] && [ "$2" = "$PWD" ] '
              '&& [ "$3" = compiled-fib-test ] || exit 97\n'
              'printf "regressions\\n" >> "$CALLS"\n'
              # The real suite also exercises run_regressions and emits its
              # own decisions. Only the outer consumer's first line is public.
              'printf "LEAN_INSPECTOR_FIB_REGRESSIONS changed=true selected=true\\n"\n'
              'printf "regression stdout detail\\n"\nprintf "regression stderr detail\\n" >&2\n'
              'exit ' + str(failure) + '\n')
        write('tools/scripts/auric-fib-analysis.sh', '#!/bin/sh\n'
              'printf "unexpected analyzer\\n" >> "$CALLS"\nexit 98\n')
        producer = write('producer.dll', 'fixture producer')
        shell_environment = write('shell-env', 'unset SECONDS\n' if unavailable_clock else '')
        calls = root / 'calls'
        logs = root / 'logs'
        environment = dict(os.environ,
            PATH=os.pathsep.join((str(root / 'bin'), str(Path(sys.executable).resolve().parent), os.environ['PATH'])),
            CALLS=str(calls), LAKE_BIN=str(root / 'bin/lake'),
            STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_BUILD_TARGETS='[]',
            STRATALINT_LEAN_PRODUCER_DLL=str(producer),
            STRATALINT_FIB_REGRESSIONS_SELECTED=str(selected).lower(),
            STRATALINT_LEAN_REPORT_REUSE=str(report), BASH_ENV=str(shell_environment))
        result = subprocess.run(['bash', str(root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(root), '--output', str(report), '--log-dir', str(logs), '--regenerate-report-artifacts', str(int(regenerate))],
            cwd=report.parent, env=environment, capture_output=True, text=True, timeout=30)
        actual_calls = calls.read_text().splitlines() if calls.exists() else []
        return result, actual_calls, report, logs, before

    def test_explicit_recovery_rejects_old_comparison_and_runs_exactly_one_suite(self):
        for failure in (0, 41):
            with self.subTest(failure=failure):
                result, calls, report, logs, before = self.entry(regenerate=True, obsolete=True, failure=failure)
                self.assertEqual(result.returncode, failure, result.stdout + result.stderr)
                self.assertEqual(calls, ['ensure', 'report', 'regressions'])
                self.assertEqual(publication.member(report, '.reuse.json').exists(), failure == 0)
                if failure:
                    self.assertEqual(before, {suffix: publication.member(report, suffix).read_bytes()
                                              for suffix in publication.SUFFIXES})
                    self.assertNotIn('phase=publish ', result.stderr)
                else:
                    self.assertIn('phase=publish status=completed', result.stderr)
                    self.assertNotIn('schema_version', report.read_text())

    def test_recovery_does_not_relax_fresh_validation_or_normal_predecessor_errors(self):
        for regenerate, obsolete, invalid_fresh in ((False, True, False), (True, True, True)):
            with self.subTest(regenerate=regenerate, invalid_fresh=invalid_fresh):
                result, calls, report, logs, before = self.entry(regenerate=regenerate,
                    obsolete=obsolete, invalid_fresh=invalid_fresh)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn('fib.invalid_partition', result.stderr)
                self.assertNotIn('regressions', calls)
                self.assertFalse(publication.member(report, '.reuse.json').exists())
                self.assertEqual(before, {suffix: publication.member(report, suffix).read_bytes()
                                          for suffix in publication.SUFFIXES})

    def test_valid_recovery_predecessor_keeps_equal_input_and_selection_decisions(self):
        for changed, selected in ((False, False), (True, False), (False, True)):
            with self.subTest(changed=changed, selected=selected):
                result, calls, _, _, _ = self.entry(regenerate=True, changed=changed, selected=selected)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertEqual(calls, ['ensure', 'report'] + (['regressions'] if changed or selected else []))

    def test_successful_fresh_decisions_run_or_skip_without_test_log_dump(self):
        for changed in (False, True):
            for selected in (False, True):
                for unavailable_clock in (False, True):
                    with self.subTest(changed=changed, selected=selected, unavailable_clock=unavailable_clock):
                        result, calls, report, logs, _ = self.entry(changed=changed,
                            selected=selected, unavailable_clock=unavailable_clock)
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                        decision = ('LEAN_INSPECTOR_FIB_REGRESSIONS changed=' + str(changed).lower()
                                    + ' selected=' + str(selected).lower())
                        self.assertEqual([line for line in result.stderr.splitlines()
                            if line.startswith('LEAN_INSPECTOR_FIB_REGRESSIONS ')], [decision])
                        self.assertNotIn(decision, result.stdout)
                        self.assertEqual(calls, ['ensure', 'report'] +
                                         (['regressions'] if changed or selected else []))
                        self.assertNotIn('regression stdout detail', result.stdout + result.stderr)
                        self.assertNotIn('regression stderr detail', result.stdout + result.stderr)
                        if changed or selected:
                            self.assertIn('regression stdout detail', (logs / 'fib-regressions.stdout.log').read_text())
                            self.assertIn('regression stderr detail', (logs / 'fib-regressions.stderr.log').read_text())
                        self.assertEqual((logs / 'fib-regressions.exit.log').read_text(), '0\n')
                        if unavailable_clock:
                            self.assertIn('elapsed_seconds=unavailable exit=0', result.stderr)
                        self.assertIn('phase=publish status=completed', result.stderr)
                        self.assertTrue(publication.member(report, '.reuse.json').is_file())

    def test_accepted_reuse_reports_decision_without_extra_work_or_row_reads(self):
        for selected in (False, True):
            for failure in ((0, 41) if selected else (0,)):
                for unavailable_clock in (False, True):
                    with self.subTest(selected=selected, failure=failure, unavailable_clock=unavailable_clock):
                        result, calls, report, logs, before = self.entry(cached=True, selected=selected,
                            failure=failure, unavailable_clock=unavailable_clock)
                        self.assertEqual(result.returncode, failure, result.stdout + result.stderr)
                        decision = ('LEAN_INSPECTOR_FIB_REGRESSIONS changed=false selected=' + str(selected).lower())
                        self.assertEqual(result.stderr.splitlines().count(decision), 1)
                        self.assertNotIn(decision, result.stdout)
                        self.assertEqual(calls, ['regressions'] if selected else [])
                        self.assertEqual((logs / 'fib-regressions.exit.log').exists(), selected)
                        self.assertNotIn('phase=report ', result.stderr)
                        self.assertEqual(report.read_bytes(), before[''])
                        # Reuse already published/resealed the accepted generation;
                        # a later explicit regression failure does not undo that.
                        self.assertEqual(json.loads(publication.member(report, '.provenance.json').read_text())['mode'], 'cached')
                        self.assertTrue(publication.member(report, '.reuse.json').is_file())
                        if failure:
                            self.assertIn('LEAN_INSPECTOR_FAILED phase=fib-regressions exit=41', result.stderr)
                            self.assertIn('regression stderr detail', result.stderr)
                        else:
                            self.assertEqual([line for line in result.stderr.splitlines()
                                if line.startswith('LEAN_INSPECTOR_FIB_REGRESSIONS ')], [decision])
                            self.assertNotIn('regression stderr detail', result.stderr)

    def test_fresh_failure_preserves_all_public_members_and_exact_exit(self):
        for changed, selected, missing in ((True, False, False), (False, True, False),
                                          (True, False, True)):
            with self.subTest(changed=changed, selected=selected, missing=missing):
                result, calls, report, logs, before = self.entry(changed=changed, selected=selected,
                    failure=41, missing_inputs=missing)
                status = 1 if missing else 41
                self.assertEqual(result.returncode, status, result.stdout + result.stderr)
                self.assertIn(f'LEAN_INSPECTOR_FAILED phase=fib-regressions exit={status}', result.stderr)
                self.assertEqual((logs / 'fib-regressions.exit.log').read_text(), str(status) + '\n')
                self.assertEqual(calls, ['ensure', 'report'] + ([] if missing else ['regressions']))
                self.assertEqual(before, {suffix: publication.member(report, suffix).read_bytes()
                                          for suffix in publication.SUFFIXES})
                self.assertFalse(publication.member(report, '.reuse.json').exists())
                self.assertNotIn('phase=publish ', result.stderr)
                if missing:
                    self.assertIn('fib.missing_required_inputs', result.stderr)
                    self.assertNotIn('LEAN_INSPECTOR_FIB_REGRESSIONS changed=', result.stderr)
                else:
                    self.assertIn('regression stdout detail', result.stderr)
                    self.assertIn('regression stderr detail', result.stderr)


if __name__ == '__main__':
    unittest.main()
