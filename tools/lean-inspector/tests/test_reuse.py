"""Behavioral contract for optional, complete report-entry reuse receipts."""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import zipfile
import zlib

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import materials
import publication

EXECUTION = dict(tools=['lake', 'lean'], platform=['system', 'machine'],
    environment=['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN', 'LEAN_OPTS'])


class ReuseTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='report entry reuse ')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        paths = lambda *values: dict(include=[dict(pattern=v, optional=False) for v in values], exclude=[])
        self.policy = dict(schema_version=1, report_semantic_version=1,
            report_modules=paths('D5/**/*.lean'), inspector_sources=paths('Inspector.lean'),
            dependency_sources=paths('Audit.lean'), config_inputs=paths('lean-toolchain', 'lakefile.toml'),
            producer_scopes={'lean-report': paths('lean-report-inputs.json',
                'tools/scripts/report/lean-report-selection.py', 'producer.py'),
                'scribe-content': dict(include=[], exclude=[])}, report_execution=copy.deepcopy(EXECUTION))
        for path, value in {'D5/A.lean': 'def a := 1\n', 'Audit.lean': 'def audit := 1\n',
                'Inspector.lean': 'def inspector := 1\n', 'producer.py': '# producer\n',
                'lean-toolchain': 'fixture\n', 'lakefile.toml': 'name = "fixture"\n'}.items():
            self.write(path, value)
        self.write_policy()
        for name in ['tools/scripts/report/lean-report-selection.py', 'tools/scripts/report/lean-report-input.sh',
                'tools/scripts/worktree/lean-cache-input.sh']:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / name, path)
            path.chmod(0o755)
        self.lake = self.root / 'bin/lake'
        for name in EXECUTION['tools']:
            path = self.root / 'bin' / name
            path.parent.mkdir(exist_ok=True)
            path.write_text('#!/bin/sh\n[ "$1" = --version ] || exit 91\nprintf "%s\\n" "fixture ' + name + ' 1"\n')
            path.chmod(0o755)
        self.report = self.root / 'seed' / publication.RAW
        self.report.parent.mkdir()
        self.output = self.root / 'output' / publication.RAW
        self.environment = patch.dict(os.environ, {name: '' for name in EXECUTION['environment']})
        self.environment.start()
        self.addCleanup(self.environment.stop)

    def write(self, path, value):
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)

    def write_policy(self):
        self.write('lean-report-inputs.json', json.dumps(self.policy))

    def bundle(self):
        inputs = publication.selection.Selection(self.root)
        rows = [dict(module=name, source_path=path,
                     source_sha256='sha256:' + publication.digest(inputs.safe_file(path)),
                     imports=[], declarations=[]) for name, path in sorted(inputs.modules().items())]
        self.report.write_bytes(materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=rows)))
        with zipfile.ZipFile(publication.member(self.report, '.materials.zip'), 'w'):
            pass
        origins = {row['module']: dict(module=row['module'],
            report_sha256=hashlib.sha256(materials.canonical_json(
                dict(schema=materials.REPORT_SCHEMA, modules=[row]))).hexdigest(),
            compatibility_sha256=inputs.compatibility(), producer_sources_sha256='a' * 64,
            inspector_executable_sha256='b' * 64,
            input_sources={row['source_path']: row['source_sha256'][7:]}) for row in rows}
        publication.write_sidecars(self.report, publication.coordinates(self.root), origins)

    def receipt(self):
        import reuse
        self.bundle()
        captured = reuse.capture(self.root, self.lake)
        reuse.seal(self.root, self.report, self.lake, captured)
        return reuse

    def test_execution_registration_is_explicit_and_strict(self):
        try:
            publication.selection.Selection(self.root).validate('lean-report')
        except ValueError as error:
            self.fail('[FAIL] registered_execution_rejected: ' + str(error))
        original = copy.deepcopy(self.policy)
        for bad in [None, {}, dict(EXECUTION, tools=['lake', 'shell']),
                    dict(EXECUTION, tools=['lake']), dict(EXECUTION, platform=['system', 'system']),
                    dict(EXECUTION, environment=['PATH']), dict(EXECUTION, commands=['anything'])]:
            with self.subTest(contract=bad):
                self.policy['report_execution'] = bad
                self.write_policy()
                with self.assertRaisesRegex(ValueError, 'report_execution'):
                    publication.selection.Selection(self.root)
        self.policy = original
        del self.policy['report_execution']
        self.write_policy()
        publication.selection.Selection(self.root).validate('lean-report')

    def test_complete_receipt_accepts_unchanged_input_without_lake_build(self):
        api = self.receipt()
        with patch.object(publication, 'validate_bundle', wraps=publication.validate_bundle) as validation, \
                patch.object(publication, 'coordinates', wraps=publication.coordinates) as coordinates:
            self.assertFalse(api.probe(self.root, self.report, self.lake)['needs_lake'])
            self.assertEqual(validation.call_count, 0, '[FAIL] probe_must_not_repeat_publication_validation')
            self.assertEqual(coordinates.call_count, 0, '[FAIL] probe_must_not_prepare_publication')
            self.assertFalse(self.output.exists())
            self.assertFalse((self.root / '.lake').exists())
            self.assertFalse(api.reuse(self.root, self.report, self.output, self.lake)['needs_lake'])
            self.assertEqual(validation.call_count, 1, '[FAIL] normal_entry_must_validate_publication')
        publication.validate_bundle(self.output, publication.coordinates(self.root), self.root)
        self.assertEqual(json.loads(publication.member(self.output, '.provenance.json').read_text())['mode'], 'cached')
        self.assertFalse(api.probe(self.root, self.output, self.lake)['needs_lake'])
        self.assertFalse(api.reuse(self.root, self.output, self.output, self.lake)['needs_lake'])
        self.assertFalse((self.root / '.lake').exists())

    def test_probe_cli_reports_misses_but_rejects_invalid_registration(self):
        self.receipt()
        command = [sys.executable, '-B', str(HERE / 'reuse.py'), 'probe', '--repository', str(self.root),
                   '--report', str(self.report), '--lake', str(self.lake)]
        accepted = subprocess.run(command, text=True, capture_output=True, check=False)
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertFalse(json.loads(accepted.stdout)['needs_lake'])
        publication.member(self.report, '.reuse.json').unlink()
        missed = subprocess.run(command, text=True, capture_output=True, check=False)
        self.assertEqual(missed.returncode, 0, missed.stderr)
        self.assertTrue(json.loads(missed.stdout)['needs_lake'])
        self.policy['report_execution']['tools'] = ['arbitrary-command']
        self.write_policy()
        invalid = subprocess.run(command, text=True, capture_output=True, check=False)
        self.assertNotEqual(invalid.returncode, 0)
        self.assertIn('report_execution.tools', invalid.stderr)
        self.assertEqual(invalid.stdout, '')

    def test_input_changes_additions_deletions_and_environment_invalidate_receipt(self):
        api = self.receipt()
        for path in ['D5/A.lean', 'Audit.lean', 'Inspector.lean',
                     'lean-toolchain', 'lakefile.toml']:
            with self.subTest(changed=path):
                source = self.root / path
                original, stamp = source.read_bytes(), source.stat()
                source.write_bytes(original + b'\n')
                os.utime(source, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
                self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])
                source.write_bytes(original)
        self.write('D5/New.lean', 'def fresh := 2\n')
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])

        api = self.receipt()
        (self.root / 'D5/New.lean').unlink()
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])
        api = self.receipt()
        for name in EXECUTION['environment']:
            with self.subTest(environment=name), patch.dict(os.environ, {name: 'changed'}):
                self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])
        with patch.object(api.platform, 'machine', return_value='another-architecture'):
            self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])
        self.lake.write_text(self.lake.read_text().replace('lake 1', 'lake 2'))
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])

    def test_registered_file_mode_changes_invalidate_reuse_and_sealing(self):
        api = self.receipt()
        captured = api.capture(self.root, self.lake)
        source = self.root / 'Audit.lean'
        source.chmod(0o755)
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'],
                        '[FAIL] lean_source_mode_change_invalidates_reuse')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            api.seal(self.root, self.report, self.lake, captured)

    def test_producer_program_bytes_never_gate_reuse(self):
        api = self.receipt()
        captured = api.capture(self.root, self.lake)
        producer_only = ['producer.py', 'tools/scripts/report/lean-report-selection.py']
        self.assertTrue(all(path.endswith('.lean') or path in ('lean-toolchain', 'lakefile.toml')
                            for path in captured['files']),
                        '[FAIL] receipt_population_is_lean_and_configuration_only: ' + repr(sorted(captured['files'])))
        self.assertFalse(set(producer_only + ['lean-report-inputs.json']) & set(captured['files']),
                         '[FAIL] producer_program_not_hashed')
        for path in producer_only:
            with self.subTest(changed=path):
                source = self.root / path
                original, mode = source.read_bytes(), source.stat().st_mode
                source.write_bytes(original + b'\n# producer-only edit\n')
                source.chmod(0o700)
                self.assertEqual(api.probe(self.root, self.report, self.lake),
                                 dict(needs_lake=False, reason='receipt-matched'),
                                 '[FAIL] producer_program_change_keeps_receipt')
                source.write_bytes(original)
                source.chmod(mode)
        self.policy['report_semantic_version'] += 1
        self.write_policy()
        result = api.probe(self.root, self.report, self.lake)
        self.assertTrue(result['needs_lake'] and result['reason'] == 'seed-rejected',
                        '[FAIL] semantic_version_bump_rejects_seed: ' + repr(result))

    def test_legacy_and_corrupt_receipts_and_bundles_require_lake(self):
        api = self.receipt()
        suffixes = (*publication.SUFFIXES, '.reuse.json')
        for suffix in suffixes:
            path = publication.member(self.report, suffix)
            original = path.read_bytes()
            for damage in ['missing', 'corrupt', 'symlink']:
                with self.subTest(suffix=suffix, damage=damage):
                    path.unlink()
                    if damage == 'corrupt':
                        path.write_bytes(b'corrupt')
                    elif damage == 'symlink':
                        target = self.root / 'alias'
                        target.write_bytes(original)
                        path.symlink_to(target)
                    self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])
                    self.assertTrue(api.reuse(self.root, self.report, self.output, self.lake)['needs_lake'])
                    path.unlink(missing_ok=True)
                    path.write_bytes(original)
        receipt = publication.member(self.report, '.reuse.json')
        record = json.loads(receipt.read_text())
        record['completed'] = ['report', 'publication']
        receipt.write_text(json.dumps(record))
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])

    def test_validation_uses_material_reader_and_private_publication(self):
        api = self.receipt()
        validator = publication.validate_bundle
        def mutate_private(report, *args, **kwargs):
            result = validator(report, *args, **kwargs)
            if '.lean-report.' in str(report):
                publication.member(report, '.materials.zip').write_bytes(b'changed during validation')
            return result
        with patch.object(publication, 'validate_bundle', side_effect=mutate_private):
            self.assertTrue(api.reuse(self.root, self.report, self.output, self.lake)['needs_lake'])
        self.assertFalse(self.output.exists())
        # Matching receipt hashes cannot bypass the semantic/material validator.
        archive = publication.member(self.report, '.materials.zip')
        with zipfile.ZipFile(archive, 'w') as out:
            out.writestr('unreferenced', b'bytes')
        receipt = publication.member(self.report, '.reuse.json')
        record = json.loads(receipt.read_text())
        record['bundle']['.materials.zip'] = publication.digest(archive)
        receipt.write_text(json.dumps(record))
        self.assertFalse(api.probe(self.root, self.report, self.lake)['needs_lake'],
                         '[FAIL] probe_only_selects_resources')
        self.assertTrue(api.reuse(self.root, self.report, self.output, self.lake)['needs_lake'],
                        '[FAIL] sealed_hashes_cannot_authorize_bad_materials')
        self.assertFalse(self.output.exists())

    def test_optional_decoder_damage_is_a_miss_but_programming_errors_escape(self):
        api = self.receipt()
        errors = [zlib.error('broken DEFLATE seed'), NotImplementedError('unsupported ZIP method')]
        if zipfile.lzma is not None:
            errors.append(zipfile.lzma.LZMAError('broken LZMA seed'))
        for error in errors:
            with self.subTest(error=type(error).__name__), patch.object(
                    publication, 'validate_bundle', side_effect=error):
                try:
                    self.assertFalse(api.probe(self.root, self.report, self.lake)['needs_lake'])
                    self.assertTrue(api.reuse(self.root, self.report, self.output, self.lake)['needs_lake'])
                except type(error):
                    self.fail('[FAIL] optional_decoder_error_must_request_lake')
        with patch.object(publication, 'validate_bundle', side_effect=AssertionError('programming error')):
            self.assertFalse(api.probe(self.root, self.report, self.lake)['needs_lake'])
            with self.assertRaisesRegex(AssertionError, 'programming error'):
                api.reuse(self.root, self.report, self.output, self.lake)

    def test_semantic_seed_miss_preserves_absent_destination_parents(self):
        api = self.receipt()
        archive = publication.member(self.report, '.materials.zip')
        with zipfile.ZipFile(archive, 'w') as out:
            out.writestr('unreferenced', b'bytes')
        receipt = publication.member(self.report, '.reuse.json')
        record = json.loads(receipt.read_text())
        record['bundle']['.materials.zip'] = publication.digest(archive)
        receipt.write_text(json.dumps(record))
        output = self.root / '.lake/build/stratalint' / publication.RAW
        self.assertTrue(api.reuse(self.root, self.report, output, self.lake)['needs_lake'])
        self.assertFalse((self.root / '.lake').exists(), '[FAIL] rejected_seed_created_cold_lake')

    def test_private_publication_must_match_the_sealed_bytes(self):
        api = self.receipt()
        publish = publication.publish
        def replace_seed_before_snapshot(*args, **kwargs):
            provenance = publication.member(self.report, '.provenance.json')
            record = json.loads(provenance.read_text())
            record['mode'] = 'cached'
            provenance.write_text(json.dumps(record, separators=(',', ':')) + '\n')
            return publish(*args, **kwargs)
        with patch.object(publication, 'publish', side_effect=replace_seed_before_snapshot):
            self.assertTrue(api.reuse(self.root, self.report, self.report, self.lake)['needs_lake'])
        self.assertFalse(publication.member(self.report, '.reuse.json').exists())

    def test_seal_and_reuse_reject_input_changes_during_work(self):
        api = self.receipt()
        captured = api.capture(self.root, self.lake)
        self.write('Audit.lean', 'def audit := 2\n')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            api.seal(self.root, self.report, self.lake, captured)
        api = self.receipt()
        publish = publication.publish
        def mutate_after_publish(*args, **kwargs):
            publish(*args, **kwargs)
            self.write('Audit.lean', 'def audit := 3\n')
        with patch.object(publication, 'publish', side_effect=mutate_after_publish):
            self.assertTrue(api.reuse(self.root, self.report, self.output, self.lake)['needs_lake'])
        self.assertFalse(publication.member(self.output, '.reuse.json').exists())

    def test_missing_execution_contract_disables_only_reuse(self):
        api = self.receipt()
        del self.policy['report_execution']
        self.write_policy()
        captured = api.capture(self.root, self.lake)
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])
        api.seal(self.root, self.report, self.lake, captured)
        self.assertFalse(publication.member(self.report, '.reuse.json').exists())
        self.policy['report_execution'] = dict(EXECUTION, tools=['arbitrary-command'])
        self.write_policy()
        with self.assertRaisesRegex(ValueError, 'report_execution'):
            api.probe(self.root, self.report, self.lake)
        with self.assertRaisesRegex(ValueError, 'report_execution'):
            api.reuse(self.root, self.report, self.output, self.lake)

    def entry_with_program_build(self, targets, *, seed=True, build_exit=0):
        # Exercise the actual shell entry and report receipt, replacing only the
        # external cache/build processes. No Lean compilation is needed here.
        for relative in ('tools/lean-inspector/inspect.sh', 'tools/lean-inspector/reuse.py',
                         'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                         'tools/scripts/lib/resource-observation-lib.sh',
                         'tools/scripts/workflow/ci_plan.py'):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)
        ensure = self.root / 'tools/scripts/worktree/lean-cache-ensure.sh'
        ensure.write_text('#!/bin/bash\nset -euo pipefail\n'
                          'test ! -e .lake\nprintf "ensure\\n" >> build-calls\nmkdir .lake\n')
        runner = self.root / 'tools/scripts/worktree/lean-cache-run.sh'
        runner.write_text('#!/bin/bash\nset -euo pipefail\n'
                          'printf "%s\\n" "$*" >> build-calls\n'
                          'exit ' + str(build_exit) + '\n')
        runner.chmod(0o755)
        self.receipt()
        if not seed:
            publication.member(self.report, '.reuse.json').unlink()
        elif seed == 'corrupt':
            publication.member(self.report, '.reuse.json').write_text('damaged receipt')
        self.output = self.root / '.lake/build/stratalint' / publication.RAW
        producer = self.root / 'producer.dll'
        producer.write_text('fixture executable')
        environment = dict(os.environ, LAKE_BIN=str(self.lake),
            STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_PRODUCER_DLL=str(producer),
            STRATALINT_LEAN_REPORT_REUSE=str(self.report),
            STRATALINT_LEAN_BUILD_TARGETS=json.dumps(targets))
        if targets is None:
            environment.pop('STRATALINT_LEAN_BUILD_TARGETS')
            self.write('Meta/ci-resources.json', json.dumps(dict(
                schema='ci-resource-execution-v1', resources=[dict(
                    id='fixture-program-build', projects=[], checks=[], steps=[],
                    lean_targets=['FixtureAudit'])])))
        result = subprocess.run(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(self.output),
            '--log-dir', str(self.root / 'logs')], env=environment, text=True, capture_output=True)
        calls = self.root / 'build-calls'
        return result, calls.read_text().splitlines() if calls.exists() else []

    def test_exact_report_reuse_still_builds_registered_program_targets(self):
        targets = ['LeanInformationAudit', 'leanInspector/reportInspector']
        result, calls = self.entry_with_program_build(targets)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['ensure', str(self.lake) + ' build ' + ' '.join(targets)])
        self.assertEqual(self.output.read_bytes(), self.report.read_bytes())
        self.assertTrue(publication.member(self.output, '.reuse.json').is_file())

    def test_reused_report_cannot_mask_program_build_failure(self):
        result, calls = self.entry_with_program_build(['LeanInformationAudit'], build_exit=42)
        self.assertEqual(result.returncode, 42, result.stdout + result.stderr)
        self.assertEqual(len(calls), 2)
        self.assertFalse(publication.member(self.output, '.reuse.json').exists())

    def test_report_miss_combines_program_and_report_in_one_lake_build(self):
        targets = ['LeanInformationAudit', 'leanInspector/reportInspector']
        result, calls = self.entry_with_program_build(targets, seed=False, build_exit=42)
        self.assertEqual(result.returncode, 42, result.stdout + result.stderr)
        self.assertEqual(calls, ['ensure', str(self.lake) + ' build :report ' + ' '.join(targets)])

    def test_report_reuse_without_program_obligation_needs_no_build_cache(self):
        result, calls = self.entry_with_program_build([])
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, [])

    def test_corrupt_report_seed_keeps_program_build_in_normal_report_invocation(self):
        result, calls = self.entry_with_program_build(['LeanInformationAudit'], seed='corrupt', build_exit=42)
        self.assertEqual(result.returncode, 42, result.stdout + result.stderr)
        self.assertEqual(calls, ['ensure', str(self.lake) + ' build :report LeanInformationAudit'])
        self.assertFalse(publication.member(self.output, '.reuse.json').exists())

    def test_invalid_program_target_fails_before_provisioning(self):
        result, calls = self.entry_with_program_build(['--invalid-build-option'])
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertEqual(calls, [])
        self.assertIn('lean_targets requires', result.stderr)

    def test_direct_report_entry_uses_registered_program_targets(self):
        result, calls = self.entry_with_program_build(None)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(calls, ['ensure', str(self.lake) + ' build FixtureAudit'])


if __name__ == '__main__':
    unittest.main()
