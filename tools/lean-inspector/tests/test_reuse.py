"""Behavioral contract for optional, complete report-entry reuse receipts."""
import copy
import hashlib
import json
import os
from pathlib import Path
import platform
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

    def register_toolchain(self):
        self.policy['report_execution']['toolchain'] = dict(pin='fixture', identities=[dict(
            platform={name: getattr(platform, name)() for name in EXECUTION['platform']},
            tools={name: 'fixture ' + name + ' 1' for name in EXECUTION['tools']})])
        self.write_policy()

    def test_registered_toolchain_reuses_without_executing_or_installing_tools(self):
        self.register_toolchain()
        api = self.receipt()
        shutil.rmtree(self.lake.parent)
        with patch.object(subprocess, 'check_output', wraps=subprocess.check_output) as commands, \
                patch.object(publication, 'validate_bundle', wraps=publication.validate_bundle) as validation:
            self.assertFalse(api.probe(self.root, self.report, None)['needs_lake'])
            self.assertEqual(validation.call_count, 0)
            self.assertFalse(api.reuse(self.root, self.report, self.output, None)['needs_lake'])
            self.assertEqual(validation.call_count, 1, '[FAIL] tool_free_reuse_keeps_normal_publication')
            self.assertFalse(any(Path(call.args[0][0]).name in EXECUTION['tools']
                for call in commands.call_args_list), '[FAIL] lean_tools_must_remain_unused')
        publication.validate_bundle(self.output, publication.coordinates(self.root), self.root)

    def test_tool_free_reuse_requires_candidate_identity_not_donor_claims(self):
        self.register_toolchain()
        api = self.receipt()
        path = publication.member(self.report, '.reuse.json')
        sealed = path.read_bytes()
        for name in EXECUTION['tools']:
            with self.subTest(tool=name):
                receipt = json.loads(sealed)
                receipt['inputs']['execution']['tools'][name] = 'donor supplied version'
                path.write_text(json.dumps(receipt))
                self.assertTrue(api.probe(self.root, self.report, None)['needs_lake'])
                self.assertTrue(api.reuse(self.root, self.report, self.output, None)['needs_lake'])
                self.assertFalse(publication.member(self.output, '.reuse.json').exists())
        path.write_bytes(sealed)
        with patch.dict(os.environ, LEAN_OPTS='--another-option'):
            self.assertTrue(api.probe(self.root, self.report, None)['needs_lake'])
        with patch.dict(os.environ, ELAN_TOOLCHAIN='another/toolchain'):
            self.assertTrue(api.probe(self.root, self.report, None)['needs_lake'])
        with patch.object(platform, 'machine', return_value='unregistered-machine'):
            self.assertTrue(api.probe(self.root, self.report, None)['needs_lake'])
        self.write('lean-toolchain', 'another/toolchain\n')
        self.assertTrue(api.probe(self.root, self.report, None)['needs_lake'])

    def test_registered_tool_versions_are_verified_before_sealing(self):
        self.register_toolchain()
        api = self.receipt()
        self.lake.write_text('#!/bin/sh\nprintf "%s\\n" "wrong compiler"\n')
        captured = api.capture(self.root, self.lake)
        self.assertFalse(captured['eligible'], '[FAIL] actual_tool_must_match_candidate_registration')
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'])
        api.seal(self.root, self.report, self.lake, captured)
        self.assertFalse(publication.member(self.report, '.reuse.json').exists())

    def test_missing_tool_identity_and_damaged_material_need_normal_production(self):
        api = self.receipt()
        self.assertTrue(api.probe(self.root, self.report, None)['needs_lake'])
        self.register_toolchain()
        api = self.receipt()
        archive = publication.member(self.report, '.materials.zip')
        with zipfile.ZipFile(archive, 'a') as target:
            target.writestr('unregistered material', b'not a valid report material')
        # Even a self-consistent donor hash cannot grant publication success.
        path = publication.member(self.report, '.reuse.json')
        receipt = json.loads(path.read_bytes())
        receipt['bundle']['.materials.zip'] = publication.digest(archive)
        path.write_text(json.dumps(receipt))
        self.assertFalse(api.probe(self.root, self.report, None)['needs_lake'])
        self.assertTrue(api.reuse(self.root, self.report, self.output, None)['needs_lake'])
        self.assertFalse(publication.member(self.output, '.reuse.json').exists())

    def test_toolchain_registration_rejects_missing_duplicate_and_unknown_fields(self):
        self.register_toolchain()
        original = copy.deepcopy(self.policy['report_execution']['toolchain'])
        for bad in [None, {}, dict(original, pin=''), dict(original, identities=[]),
                    dict(original, identities=original['identities'] * 2),
                    dict(original, discover=True),
                    dict(original, identities=[dict(platform=original['identities'][0]['platform'], tools={})])]:
            with self.subTest(contract=bad):
                self.policy['report_execution']['toolchain'] = bad
                self.write_policy()
                with self.assertRaisesRegex(ValueError, 'report_execution.toolchain'):
                    publication.selection.Selection(self.root)

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
        for path in ['D5/A.lean', 'Audit.lean', 'Inspector.lean', 'producer.py',
                     'lean-toolchain', 'lakefile.toml', 'lean-report-inputs.json']:
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
        producer = self.root / 'producer.py'
        producer.chmod(0o755)
        self.assertTrue(api.probe(self.root, self.report, self.lake)['needs_lake'],
                        '[FAIL] producer_mode_change_invalidates_reuse')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            api.seal(self.root, self.report, self.lake, captured)

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


if __name__ == '__main__':
    unittest.main()
