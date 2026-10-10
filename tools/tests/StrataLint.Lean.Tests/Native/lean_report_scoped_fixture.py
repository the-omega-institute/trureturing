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

    def bundle(self, producer):
        row = dict(module='D5.A', source_path='D5/A.lean', imports=[], declarations=[],
                   source_sha256='sha256:' + publication.digest(self.root / 'D5/A.lean'))
        report = self.root / 'scoped.json'
        report.write_bytes(materials.canonical_json(dict(schema='stratalint-scoped-lean-report-v1', modules=[row])))
        with zipfile.ZipFile(publication.member(report, '.materials.zip'), 'w'):
            pass
        origin = dict(module='D5.A', report_sha256=hashlib.sha256(materials.canonical_json(
            dict(schema=materials.REPORT_SCHEMA, modules=[row]))).hexdigest(),
            input_projection=dict(schema='stratalint-judge-input-projection-v1', module='D5.A', inputs=[]),
            producer_sources_sha256='a' * 64, inspector_executable_sha256='b' * 64)
        producer.write_sidecars(report, producer.capture(self.root, self.scope), {'D5.A': origin})
        return report

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
            self.run_lake('-d', 'tools/lean-inspector', 'build', 'leanInspector/reportInspector')
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
                  'claim=D5/S0/Carrier/Missing.claim; result=D5/S0/Carrier/Unfinished.result\n'
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
        before = [canonical.read_bytes(), receipt.read_bytes()]
        self.write('D5/A.lean', 'import D5.B\n/- import D5.Alone /- nested comment -/ -/\ndef value : Nat := D5.hidden\n')
        self.write('D5/Alone.lean', 'this sibling deliberately does not compile\n')
        self.env['STRATALINT_LEAN_BUILD_TARGETS'] = '["reg/Reg"]'
        self.scoped('D5.A')
        self.assertEqual(set(self.rows()), {'D5.A', 'D5.B'}, '[FAIL] report_is_exact_import_closure')
        self.assertFalse((self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip').exists(),
                         '[FAIL] unrelated_module_is_never_extracted')
        self.assertEqual(before, [canonical.read_bytes(), receipt.read_bytes()], '[FAIL] whole_report_is_untouched')
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
