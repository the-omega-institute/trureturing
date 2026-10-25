"""Scoped report producer contracts in the existing Lean test project."""
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import unittest
from unittest.mock import patch
import zipfile

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT / 'tools/lean-inspector/tests'))
sys.path.insert(0, str(ROOT / 'tools/lean-inspector'))
import materials
import publication
from test_reuse import ReuseTests, EXECUTION
from test_native_support import NativeDependencyTestSupport


def api(case):
    path = ROOT / 'tools/lean-inspector/scoped.py'
    case.assertTrue(path.is_file(), '[FAIL] scoped_producer_api_exists')
    spec = importlib.util.spec_from_file_location('scoped', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ScopedContracts(unittest.TestCase):
    def setUp(self):
        self.fixture = ReuseTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.fixture.write('D5/B.lean', 'def b := 2\n')
        self.scope = dict(roots=['D5.A'], modules=[dict(module='D5.A', source_path='D5/A.lean', imports=[])],
                          dependencies=[dict(module='D5.A', source_path='D5/A.lean', imports=[])])

    def bundle(self, producer, rows=None):
        if rows is None:
            rows = [dict(module=source['module'], source_path=source['source_path'],
                         imports=source['imports'], declarations=[],
                         source_sha256='sha256:' + publication.digest(self.root / source['source_path']))
                    for source in self.scope['modules']]
        report = self.root / 'scoped.json'
        report.write_bytes(materials.canonical_json(dict(schema='stratalint-scoped-lean-report-v1', modules=rows)))
        with zipfile.ZipFile(publication.member(report, '.materials.zip'), 'w'):
            pass
        origins = {row['module']: dict(module=row['module'], report_sha256=hashlib.sha256(materials.canonical_json(
            dict(schema=materials.REPORT_SCHEMA, modules=[row]))).hexdigest(),
            input_projection=dict(schema='stratalint-judge-input-projection-v1', module=row['module'], inputs=[]),
            producer_sources_sha256='a' * 64, inspector_executable_sha256='b' * 64) for row in rows}
        producer.write_sidecars(report, producer.capture(self.root, self.scope), origins)
        return report

    def test_selected_utility_discovery_uses_production_reader(self):
        producer = api(self)
        subprocess.run(['git', 'init', '--quiet', str(self.root)], check=True, capture_output=True)
        self.fixture.write('D5/S0/Carrier/Unfinished.lean',
            '/- GID: D5/S0/Carrier/Unfinished\n'
            '   generality: G\n'
            '   mirror-B: D5/B/S0/Carrier/Unfinished\n'
            '   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)\n'
            '   anchors: []\n'
            '   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Missing.claim; '
            'result=D5/S0/Carrier/Unfinished.result; claim=D5/S0/Carrier/Missing.claim\n'
            '   digest: Selected claim sources are required. -/\n')
        cli = ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'
        full = subprocess.run(['dotnet', str(cli), 'lean-utility-input'], cwd=self.root,
                              capture_output=True, text=True)
        self.assertEqual(full.returncode, 2, full.stdout + full.stderr)
        self.assertIn('Refutation claim source is absent', full.stderr)
        temporary = self.root / 'scope-discovery'
        logs = temporary / 'logs'
        logs.mkdir(parents=True)
        entry = producer.Entry(self.root, temporary, logs)
        entry.producer = str(cli)
        original = entry.phase
        def phase(name, command):
            if name != 'scope':
                return original(name, command)
            # Only Lake's already-covered graph selection is supplied by this fixture.
            request = json.loads(Path(command[-2]).read_text())
            self.assertEqual(request['roots'], ['D5.A'])
            self.assertEqual(request['utilities'], [])
            self.assertEqual(request['utility_inputs'], [])
            Path(command[-1]).write_bytes(materials.canonical_json(self.scope))
        entry.phase = phase
        scope, utilities = entry.discover(['D5.A'])
        self.assertEqual(scope, self.scope)
        self.assertEqual(utilities, [])

    def test_rejects_empty_targets_and_canonical_destination(self):
        producer = api(self)
        for value in ('', '  \t\n', ':report', 'reg/Reg', '../D5.A', 'D5.A:report'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                producer.parse_targets(value)
        self.assertEqual(producer.parse_targets('D5.B D5.A D5.A'), ['D5.A', 'D5.B'])
        canonical = self.root / '.lake/build/stratalint/raw-lean-report.json'
        canonical.parent.mkdir(parents=True)
        canonical.write_text('whole report')
        with self.assertRaisesRegex(ValueError, 'canonical'):
            producer.check_destination(self.root, canonical)
        alias = self.root / 'whole-alias.json'
        alias.symlink_to(canonical)
        with self.assertRaisesRegex(ValueError, 'canonical'):
            producer.check_destination(self.root, alias)
        door = ROOT / 'tools/scripts/report/lean-report-scoped.sh'
        rejected = subprocess.run(['/bin/bash', str(door), '--targets', '', '--output', str(self.root / 'empty.json')],
                                  capture_output=True, text=True, cwd=self.root)
        self.assertEqual(rejected.returncode, 2, rejected.stdout + rejected.stderr)
        self.assertFalse((self.root / 'empty.json').exists(), '[FAIL] empty_scope_has_no_artifact')

    def test_cache_replacement_preserves_scoped_discovery_logs(self):
        producer = api(self)
        report = self.root / '.lake/build/stratalint/scoped.json'
        report.parent.mkdir(parents=True)
        phase = producer.Entry.phase
        def discover(entry, roots):
            entry.phase('scope', [sys.executable, '-c',
                'import shutil; shutil.rmtree(".lake"); print("scope discovered")'])
            (entry.temporary / 'selected-modules.json').write_bytes(materials.canonical_json(self.scope))
            return self.scope, []
        def fail_report(entry, name, command):
            if name == 'report':
                command = [sys.executable, '-c', 'raise SystemExit(23)']
            return phase(entry, name, command)
        with patch.object(producer.Entry, 'provision'), \
                patch.object(producer.Entry, 'discover', discover), \
                patch.object(producer.Entry, 'phase', fail_report), \
                patch.object(sys, 'argv', ['scoped.py', 'produce', '--repository', str(self.root),
                                         '--report', str(report), '--targets', 'D5.A']), \
                self.assertRaises(subprocess.CalledProcessError) as failure:
            producer.main()
        self.assertEqual(failure.exception.returncode, 23)
        logs = Path(str(report) + '.logs')
        self.assertEqual((logs / 'scope.exit.log').read_text(), '0\n')
        self.assertEqual((logs / 'scope.stdout.log').read_text(), 'scope discovered\n')
        self.assertEqual((logs / 'report.exit.log').read_text(), '23\n')
        self.assertFalse(publication.member(report, '.input.attestation').exists())

    def test_scoped_bundle_checks_independent_membership_sources_and_materials(self):
        producer = api(self)
        report = self.bundle(producer)
        producer.validate_bundle(report, self.root, self.scope)
        different = copy.deepcopy(self.scope)
        different['roots'] = ['D5.B']
        different['modules'] = different['dependencies'] = [dict(module='D5.B', source_path='D5/B.lean', imports=[])]
        with self.assertRaises(ValueError, msg='[FAIL] caller_targets_are_independent'):
            producer.validate_bundle(report, self.root, different)
        original = report.read_bytes()
        report.write_bytes(original.replace(b'"imports": []', b'"imports": ["D5.B"]'))
        with self.assertRaises(ValueError, msg='[FAIL] scoped_sidecars_reject_changed_report'):
            producer.validate_bundle(report, self.root, self.scope)
        report.write_bytes(original)
        self.fixture.write('D5/A.lean', 'def a := 3\n')
        with self.assertRaises(ValueError, msg='[FAIL] scoped_source_sha_is_current'):
            producer.validate_bundle(report, self.root, self.scope)
        self.fixture.write('D5/A.lean', 'def a := 1\n')
        publication.member(report, '.materials.zip').write_bytes(b'corrupt')
        with self.assertRaises((ValueError, zipfile.BadZipFile), msg='[FAIL] scoped_materials_are_validated'):
            producer.validate_bundle(report, self.root, self.scope)

    def test_scoped_bundle_reuses_registered_source_inventory_across_modules(self):
        producer = api(self)
        self.scope['roots'] = ['D5.A', 'D5.B']
        self.scope['modules'].append(dict(module='D5.B', source_path='D5/B.lean', imports=[]))
        self.scope['dependencies'] = copy.deepcopy(self.scope['modules'])
        report = self.bundle(producer)
        with patch.object(publication.selection, 'Selection', wraps=publication.selection.Selection) as selected:
            producer.validate_bundle(report, self.root, self.scope)
            self.assertLessEqual(selected.call_count, 2,
                                 '[FAIL] scoped_validation_must_not_rescan_registered_sources_per_module')

        rows = publication.read_json(report.read_bytes())['modules']
        rows[-1]['information_templates'] = dict(schema_version=True, inventory=[], registered=[], records=[])
        report = self.bundle(producer, rows)
        with self.assertRaisesRegex(ValueError, 'declared-template evidence',
                                    msg='[FAIL] scoped_validation_still_checks_later_module_templates'):
            producer.validate_bundle(report, self.root, self.scope)

    def test_scoped_inputs_exclude_siblings_and_program_bytes(self):
        producer = api(self)
        report = self.bundle(producer)
        before = producer.capture(self.root, self.scope)
        self.fixture.write('D5/B.lean', 'def b := 99\n')
        self.fixture.write('producer.py', '# changed implementation\n')
        self.fixture.write('Inspector.lean', '-- changed implementation\n')
        self.assertEqual(before, producer.capture(self.root, self.scope), '[FAIL] scoped_reuse_has_only_data_inputs')
        producer.validate_bundle(report, self.root, self.scope)
        self.fixture.write('lean-toolchain', 'changed pin\n')
        self.assertNotEqual(before, producer.capture(self.root, self.scope))
        with self.assertRaises(ValueError, msg='[FAIL] scoped_configuration_is_current'):
            producer.validate_bundle(report, self.root, self.scope)

    def test_scoped_output_cannot_overlap_any_full_bundle_member(self):
        producer = api(self)
        canonical = self.root / '.lake/build/stratalint/raw-lean-report.json'
        canonical.parent.mkdir(parents=True)
        for suffix in (*publication.SUFFIXES, '.reuse.json'):
            protected = publication.member(canonical, suffix)
            protected.write_text('protected full output')
            with self.subTest(suffix=suffix), self.assertRaisesRegex(ValueError, 'canonical',
                    msg='[FAIL] scoped_output_protects_full_bundle_' + suffix):
                producer.check_destination(self.root, protected)

    def test_scoped_output_preserves_full_seed_base(self):
        producer = api(self)
        seed_base = self.root / '.lake/lean-report-seed-base.json'
        seed_base.parent.mkdir(parents=True)
        with self.assertRaisesRegex(ValueError, 'canonical'):
            producer.check_destination(self.root, seed_base)
        seed_base.write_text('accepted full seed generation')
        alias = self.root / 'seed-base-alias.json'
        os.link(seed_base, alias)
        with self.assertRaisesRegex(ValueError, 'canonical'):
            producer.check_destination(self.root, alias)
        with self.assertRaisesRegex(ValueError, 'canonical'):
            producer.check_destination(self.root, self.root / '.lake/../.lake/lean-report-seed-base.json')
        self.assertEqual(seed_base.read_text(), 'accepted full seed generation')


class NativeScopedContracts(NativeDependencyTestSupport, unittest.TestCase):
    def setUp(self):
        super().setUp()
        api(self)
        for name in ('tools/lean-inspector/scoped.py', 'tools/scripts/report/lean-report-scoped.sh'):
            self.copy(name)
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_execution'] = copy.deepcopy(EXECUTION)
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.output = self.root / 'reports/scoped report.json'
        self.logs = self.root / 'scoped logs'

    def scoped(self, targets, success=True):
        if self.compiler_seed is not None:
            # Restore both tools in the workspace used by scoped production.
            # Compiler preparation must not compile any project/report inputs.
            prepared = self.run_lake('--no-build', '-d', 'tools/lean-inspector-reg', 'build',
                                     'leanInspector/reportInspector', 'leanInspector/inputDiscovery')
            self.record_result('compiler-restore', dict(raw_exit=prepared.returncode,
                stdout=prepared.stdout, stderr=prepared.stderr))
        result = self.guarded_command(['/bin/bash', str(self.root / 'tools/scripts/report/lean-report-scoped.sh'),
            '--targets', targets, '--output', str(self.output), '--log-dir', str(self.logs)], cwd=self.root, env=self.env)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def verify(self, targets, success=True):
        result = self.guarded_command(['/bin/bash', str(self.root / 'tools/scripts/report/lean-report-input.sh'),
            'verify-scoped', '--repository', str(self.root), '--report', str(self.output), '--targets', targets],
            cwd=self.root, env=self.env)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def rows(self):
        value = json.loads(self.output.read_text())
        self.assertEqual(set(value), {'modules', 'schema'})
        self.assertEqual(value['schema'], 'stratalint-scoped-lean-report-v1')
        return {row['module']: row for row in value['modules']}

    def test_native_selected_utility_reader_ignores_unrelated_unfinished_refutation(self):
        self.ensure()
        # Keep cache operations on the fixture carrier, but use the production utility reader.
        carrier = self.root / 'bin/dotnet'
        script = carrier.read_text()
        boundary = 'if "--scope" in sys.argv:'
        script = script.replace(boundary,
            'if "lean-utility-input" in sys.argv: os.execv(dotnet, [dotnet, cli, *sys.argv[2:]])\n' + boundary)
        carrier.write_text(script)
        header = ('/- GID: D5/S0/Carrier/Unfinished\n'
                  '   generality: G\n'
                  '   mirror-B: D5/B/S0/Carrier/Unfinished\n'
                  '   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)\n'
                  '   anchors: []\n'
                  '   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Carrier/Missing.claim; '
                  'result=D5/S0/Carrier/Unfinished.result; claim=D5/S0/Carrier/Missing.claim\n'
                  '   digest: Selected refutations require their claim source. -/\n')
        self.write('D5/S0/Carrier/Unfinished.lean', header + 'this unrelated unfinished module does not compile\n')
        full = subprocess.run([self.dotnet, str(self.cli), 'lean-utility-input'],
                              cwd=self.root, capture_output=True, text=True)
        self.assertEqual(full.returncode, 2, full.stdout + full.stderr)
        self.assertIn('Refutation claim source is absent', full.stderr)
        self.scoped('D5.A')
        self.assertEqual(set(self.rows()), {'D5.A', 'D5.B'})
        self.verify('D5.A')
        failed = self.scoped('D5.S0.Carrier.Unfinished', success=False)
        self.assertNotEqual(failed.returncode, 0)
        self.assertIn('D5/S0/Carrier/Missing.lean', failed.stdout + failed.stderr)
        self.assertFalse(publication.member(self.output, '.input.attestation').exists())

    def test_native_scope_uses_only_explicit_module_facets(self):
        self.ensure()
        canonical = self.root / '.lake/build/stratalint/raw-lean-report.json'
        canonical.parent.mkdir(parents=True, exist_ok=True)
        canonical.write_text('deliberately unreadable full report')
        receipt = publication.member(canonical, '.reuse.json')
        receipt.write_text('deliberately unreadable whole receipt')
        seed_base = self.root / '.lake/lean-report-seed-base.json'
        seed_base.write_text('full seed generation metadata')
        full_archive = self.root / '.lake/build/lean-inspector/report.zip'
        full_archive.parent.mkdir(parents=True, exist_ok=True)
        full_archive.write_bytes(b'previous whole-report archive')
        protected = [canonical, receipt, seed_base, full_archive]
        before = [path.read_bytes() for path in protected]
        self.write('D5/A.lean', 'import D5.B\n/- import D5.Alone /- nested comment -/ -/\ndef value : Nat := D5.hidden\n')
        self.write('D5/Alone.lean', 'this sibling deliberately does not compile\n')
        self.env['STRATALINT_LEAN_BUILD_TARGETS'] = '["reg/Reg"]'
        self.scoped('D5.A')
        self.assertEqual(set(self.rows()), {'D5.A', 'D5.B'}, '[FAIL] report_is_exact_import_closure')
        phases = [json.loads(line) for line in (self.logs / 'native-phases.jsonl').read_text().splitlines()]
        inspections = [row for row in phases if row['phase'] == 'native-inspect' and row['boundary'] == 'start']
        self.assertEqual(len(inspections), 1, '[FAIL] selected_modules_share_one_native_inspection_batch')
        cold_work = json.loads((self.logs / 'work.json').read_text())
        build_log = ''.join((self.logs / ('report.' + stream + '.log')).read_text()
                            for stream in ('stdout', 'stderr'))
        self.record_result('cold-scope', cold_work, paths=[self.logs / 'work.json',
            self.logs / 'report.stdout.log', self.logs / 'report.stderr.log'])
        self.assertIn('Built Inspector native production batch', build_log)
        self.assertEqual(cold_work['extracted_module_names'], ['D5.A', 'D5.B'])
        self.assertEqual(cold_work['compiled_module_names'],
                         ['D5.A', 'D5.B'])
        self.assertFalse((self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip').exists(),
                         '[FAIL] unrelated_module_is_never_extracted')
        self.assertEqual(before, [path.read_bytes() for path in protected],
                         '[FAIL] whole_report_and_seed_base_are_untouched')
        self.assertFalse(publication.member(self.output, '.reuse.json').exists())
        self.verify('D5.A')
        self.verify('D5.B', success=False)
        self.scoped('D5.A')
        work = json.loads((self.logs / 'work.json').read_text())
        self.assertEqual(work['selected_modules'], 2)
        self.assertEqual(work['extracted_modules'], 0, '[FAIL] traced_module_facets_reuse_warm_artifacts')
        self.assertIsInstance(work['compiled_modules'], int)

    def test_native_scope_tracks_changed_imports_and_external_utility_claims(self):
        self.ensure()
        self.scoped('D5.A')
        self.write('D5/A.lean', 'import D5.Alone\ndef value : Nat := 7\n')
        self.verify('D5.A', success=False)
        self.scoped('D5.A')
        self.assertEqual(set(self.rows()), {'D5.A', 'D5.Alone'})
        self.verify('D5.A')
        self.scoped('Fixture')
        self.assertEqual(set(self.rows()), {'Fixture', 'D5.A', 'D5.Alone'})
        scope = json.loads((self.logs / 'selected-modules.json').read_text())
        self.assertTrue({'External', 'ClaimSupport'} <= {row['module'] for row in scope['dependencies']},
                        '[FAIL] utility_claim_closure_is_authoritative')
        self.verify('Fixture')
        self.write('ClaimSupport.lean', 'def claimSupport : Prop := True\n')
        self.verify('Fixture', success=False)

    def test_native_aged_warm_scope_reuses_cache_without_archive_refresh(self):
        self.scoped('D5.A')
        marker = self.root / '.lake/build/.release-refreshed-at'
        marker.write_text('2000-01-01T00:00:00+00:00\n')
        before = marker.read_bytes()
        attempted = self.root / 'archive-attempted'
        self.write('tools/scripts/worktree/lean-cache-publish.sh',
                   '#!/bin/bash\ntouch archive-attempted\nexit 79\n')

        self.scoped('D5.A')
        self.verify('D5.A')
        self.assertFalse(attempted.exists(), '[FAIL] warm_scope_needs_no_archive_transport')
        self.assertEqual(marker.read_bytes(), before, '[FAIL] scope_does_not_rejuvenate_archive_age')
        self.assertEqual(json.loads((self.logs / 'work.json').read_text())['extracted_modules'], 0)
        receipt = next(line.removeprefix('LEAN_CACHE ') for line in
                       (self.logs / 'scope.stdout.log').read_text().splitlines() if line.startswith('LEAN_CACHE '))
        self.assertEqual(json.loads(receipt)['archive_status'], 'not_attempted')

        # Explicit cache maintenance keeps its refresh behavior on the same cache.
        self.ensure()
        self.assertTrue(attempted.exists(), '[FAIL] standalone_ensure_still_refreshes_aged_cache')

    def test_native_cached_scope_still_builds_program_and_clears_failure_seal(self):
        self.ensure()
        self.scoped('D5.A')
        before = (self.root / '.lake/build/lean-inspector/modules/D5.A.zip').read_bytes()
        inspector = self.root / 'tools/lean-inspector/Inspector.lean'
        inspector.write_text(inspector.read_text() + '\n-- compatible producer edit\n')
        self.scoped('D5.A')
        self.assertEqual(json.loads((self.logs / 'work.json').read_text())['extracted_modules'], 0,
                         '[FAIL] program_bytes_do_not_invalidate_scoped_module_data')
        self.assertEqual(before, (self.root / '.lake/build/lean-inspector/modules/D5.A.zip').read_bytes())
        inspector.write_text('this producer deliberately does not compile\n')
        failed = self.scoped('D5.A', success=False)
        self.assertNotEqual(failed.returncode, 0, '[FAIL] cached_report_cannot_hide_program_build_failure')
        self.assertFalse(publication.member(self.output, '.input.attestation').exists(),
                         '[FAIL] failed_scoped_entry_has_no_success_seal')

    def test_native_scope_includes_external_consumer_and_checks_its_closure(self):
        self.ensure()
        self.write('D5/ConsumerSupport.lean', 'def consumerSupport : Nat := 1\n')
        self.write('D5/Consumer.lean', 'import D5.A\nimport D5.ConsumerSupport\n'
                   'def consumed : Nat := value + consumerSupport\n')
        self.write('D5/Alone.lean', 'this unrelated sibling deliberately does not compile\n')
        self.write('scope-inputs.json', json.dumps([
            dict(modulePath='D5/A.lean', inputModules=['D5.Consumer']),
            dict(modulePath='D5/B.lean', inputModules=['D5.Alone'])]))
        self.scoped('D5.A')
        self.assertEqual(set(self.rows()), {'D5.A', 'D5.B', 'D5.Consumer', 'D5.ConsumerSupport'},
                         '[FAIL] selected_target_consumer_and_imports_are_reported')
        self.assertFalse((self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip').exists(),
                         '[FAIL] dependency_utility_does_not_add_unrequested_reverse_dependencies')
        self.verify('D5.A')
        self.write('D5/ConsumerSupport.lean', 'def consumerSupport : Nat := 2\n')
        self.verify('D5.A', success=False)
        self.scoped('D5.A')
        self.write('D5/Consumer.lean', 'this selected consumer deliberately does not compile\n')
        self.assertNotEqual(self.scoped('D5.A', success=False).returncode, 0,
                            '[FAIL] consumer_compilation_is_required')
        self.assertFalse(publication.member(self.output, '.input.attestation').exists())


if __name__ == '__main__':
    scenario = sys.argv[1]
    owner = NativeScopedContracts if scenario.startswith('test_native_') else ScopedContracts
    unittest.main(argv=[sys.argv[0], owner.__name__ + '.' + scenario], verbosity=2)
