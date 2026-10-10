"""Behavioral contract for optional, complete report-entry reuse receipts."""
import copy
import hashlib
import io
import json
import os
from pathlib import Path
import shlex
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

EXECUTION = dict(toolchain='lean-toolchain', tools=['lake', 'lean'], platform=['system', 'machine'],
    environment=['LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'ELAN_TOOLCHAIN', 'LEAN_OPTS'])


class ReuseTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix='report entry reuse ')
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        paths = lambda *values: dict(include=[dict(pattern=v, optional=False) for v in values], exclude=[])
        self.policy = dict(schema_version=1,
            report_modules=paths('D5/**/*.lean'), inspector_sources=paths('Inspector.lean'),
            dependency_sources=paths('Audit.lean'), config_inputs=paths('lean-toolchain', 'lakefile.toml'),
            producer_scopes={'lean-report': paths('lean-report-inputs.json',
                'tools/scripts/report/lean-report-selection.py', 'producer.py'),
                'scribe-content': dict(include=[], exclude=[])}, report_execution=copy.deepcopy(EXECUTION))
        for path, value in {'D5/A.lean': 'def a := 1\n', 'Audit.lean': 'def audit := 1\n',
                'Inspector.lean': 'def inspector := 1\n', 'producer.py': '# producer\n',
                'lean-toolchain': 'fixture\n', 'lakefile.toml': 'name = "fixture"\n',
                'lake-manifest.json': json.dumps({'packages': [{'name': 'mathlib', 'rev': 'a' * 40}]})}.items():
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

            input_projection=dict(schema='stratalint-judge-input-projection-v1', module=row['module'], inputs=[]), producer_sources_sha256='a' * 64,
            inspector_executable_sha256='b' * 64) for row in rows}
        publication.write_sidecars(self.report, publication.coordinates(self.root), origins)

    def receipt(self):
        import reuse
        self.bundle()
        captured = reuse.capture(self.root)
        reuse.seal(self.root, self.report, captured, publication.bundle_identity(self.report))
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
            self.assertFalse(api.probe(self.root, self.report)['needs_lake'])
            self.assertEqual(validation.call_count, 0, '[FAIL] probe_must_not_repeat_publication_validation')
            self.assertEqual(coordinates.call_count, 0, '[FAIL] probe_must_not_prepare_publication')
            self.assertFalse(self.output.exists())
            self.assertFalse((self.root / '.lake').exists())
            self.assertFalse(api.reuse(self.root, self.report, self.output)['needs_lake'])
            self.assertEqual(validation.call_count, 1, '[FAIL] normal_entry_must_validate_publication')
        publication.validate_bundle(self.output, publication.coordinates(self.root), self.root)
        self.assertEqual(json.loads(publication.member(self.output, '.provenance.json').read_text())['mode'], 'cached')
        self.assertFalse(api.probe(self.root, self.output)['needs_lake'])
        self.assertFalse(api.reuse(self.root, self.output, self.output)['needs_lake'])
        self.assertFalse((self.root / '.lake').exists())

    def test_seed_format_requires_complete_sealed_inputs(self):
        api = self.receipt()
        receipt = publication.member(self.report, '.reuse.json')
        original = json.loads(receipt.read_text())
        invalid = [
            ('eligible', False), ('files', None), ('files', []), ('execution', None),
            ('files:D5/A.lean:sha256', 'invalid'), ('files:D5/A.lean:sha256', None),
            ('files:D5/A.lean:mode', None), ('files:D5/A.lean:mode', True),
            ('files:D5/A.lean:mode', -1), ('files:D5/A.lean:mode', 0o10000),
            ('execution:toolchain', None), ('execution:tools', None), ('execution:tools', []),
            ('execution:tools', ['lake']), ('execution:platform', []), ('execution:platform', {}),
            ('execution:platform:machine', None), ('execution:environment', []),
            ('execution:environment', {}), ('execution:environment:ELAN_TOOLCHAIN', None),
        ]
        for field, value in invalid:
            with self.subTest(field=field, value=value):
                record = copy.deepcopy(original)
                fields = field.split(':')
                target = record['inputs']
                for name in fields[:-1]:
                    target = target[name]
                target[fields[-1]] = value
                receipt.write_text(json.dumps(record))
                self.assertFalse(api.seed_format(self.report)['compatible'],
                                 '[FAIL] seed_format_requires_complete_sealed_inputs')

    def test_seed_format_requires_intact_bundle(self):
        api = self.receipt()
        receipt = publication.member(self.report, '.reuse.json')
        original = receipt.read_bytes()
        for suffix in publication.SUFFIXES:
            with self.subTest(suffix=suffix):
                record = json.loads(original)
                del record['bundle'][suffix]
                receipt.write_text(json.dumps(record))
                self.assertFalse(api.seed_format(self.report)['compatible'],
                                 '[FAIL] seed_format_requires_all_bundle_digests')
                receipt.write_bytes(original)
                member = publication.member(self.report, suffix)
                contents = member.read_bytes()
                member.write_bytes(contents + b'corrupt')
                self.assertFalse(api.seed_format(self.report)['compatible'],
                                 '[FAIL] seed_format_requires_matching_bundle_bytes')
                member.write_bytes(contents)

    def test_seed_format_requires_registered_toolchain_input(self):
        api = self.receipt()
        receipt = publication.member(self.report, '.reuse.json')
        original = json.loads(receipt.read_text())
        for files in ({}, {name: value for name, value in original['inputs']['files'].items()
                          if name != 'lean-toolchain'}):
            with self.subTest(files=files):
                record = copy.deepcopy(original)
                record['inputs']['files'] = files
                receipt.write_text(json.dumps(record))
                self.assertFalse(api.seed_format(self.report)['compatible'],
                                 '[FAIL] seed_format_requires_registered_toolchain_input')

    def test_complete_seed_format_ignores_current_inputs_and_program_bytes(self):
        api = self.receipt()
        self.write('D5/A.lean', 'def a := 2\n')
        self.write('producer.py', '# changed producer\n')
        with patch.dict(os.environ, ELAN_TOOLCHAIN='changed'), \
                patch.object(api.platform, 'machine', return_value='another-architecture'):
            self.assertEqual(api.seed_format(self.report), dict(
                report_format=publication.selection.REPORT_FORMAT, compatible=True),
                '[FAIL] complete_seed_format_does_not_compare_current_inputs')
            self.assertTrue(api.probe(self.root, self.report)['needs_lake'])

    def test_seed_base_record_is_written_after_successful_dev_seal(self):
        api = self.dev_repository()
        record = json.loads((self.root / '.lake/lean-report-seed-base.json').read_text())
        self.assertEqual(record['schema'], 'stratalint-lean-report-seed-base-v2')
        self.assertEqual(record['producer_commit_sha'],
                         subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'],
                                                 text=True).strip())
        self.assertEqual(api.seed_format(self.report)['compatible'], True)

    def test_optional_refresh_rechecks_seed_before_lake(self):
        api = self.dev_repository()
        def lose_seed(repository, report):
            publication.member(report, api.SUFFIX).unlink()
            return report
        with patch.object(api, '_refresh_stale_seed', side_effect=lose_seed), \
                patch.object(api, '_reuse') as reuse_entry:
            with self.assertRaisesRegex(api.CacheIncompatible, 'seed-unavailable-after-refresh',
                                        msg='[FAIL] refreshed_missing_seed_must_fail_closed'):
                api.recover_and_reuse(self.root, self.report, self.report)
            reuse_entry.assert_not_called()

    def test_seed_base_record_does_not_participate_in_reuse_or_compatibility(self):
        api = self.receipt()
        before = api.probe(self.root, self.report)
        path = self.root / '.lake/lean-report-seed-base.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text('{"schema":"invalid","producer_commit_sha":"not-a-sha"}\n')
        self.assertEqual(api.probe(self.root, self.report), before)
        self.assertEqual(api.seed_format(self.report),
                         {'report_format': publication.selection.REPORT_FORMAT, 'compatible': True})

    def test_canonical_reuse_preserves_original_producer(self):
        api = self.dev_repository()
        base = api.read_seed_base(self.root)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Fixture',
                        '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                        'commit', '--allow-empty', '-qm', 'unchanged report inputs'], check=True)
        self.assertFalse(api.reuse(self.root, self.report, self.report)['needs_lake'])
        self.assertEqual(base, api.read_seed_base(self.root),
                         '[FAIL] canonical_reuse_preserves_original_producer')

    def test_canonical_reuse_is_independent_of_base_record_failures(self):
        api = self.dev_repository()
        path = self.root / api.BASE_RECORD
        read_bytes = Path.read_bytes
        unlink = Path.unlink
        for failure in ('missing', 'malformed', 'unreadable', 'write-failed', 'unlink-failed'):
            with self.subTest(failure=failure):
                self.assertTrue(api.record_seed_base(self.root))
                self.assertIsNotNone(api.read_seed_base(self.root))
                if failure == 'missing':
                    path.unlink()
                elif failure in ('malformed', 'unlink-failed'):
                    path.write_text('{invalid')
                def read(source, *args, **kwargs):
                    if source == path and failure == 'unreadable':
                        raise OSError('injected base read failure')
                    return read_bytes(source, *args, **kwargs)
                def remove(source, *args, **kwargs):
                    if source == path and failure == 'unlink-failed':
                        raise OSError('injected base unlink failure')
                    return unlink(source, *args, **kwargs)
                compatible = api.seed_format(self.report)
                with patch.object(Path, 'read_bytes', read), patch.object(Path, 'unlink', remove), patch.object(api, 'record_seed_base',
                        wraps=api.record_seed_base) as record:
                    if failure == 'write-failed':
                        record.return_value = False
                    result = api.reuse(self.root, self.report, self.report)
                self.assertFalse(result['needs_lake'], '[FAIL] base_failure_does_not_block_canonical_reuse')
                self.assertFalse(api.probe(self.root, self.report)['needs_lake'])
                self.assertEqual(compatible, api.seed_format(self.report))
                api.read_receipt(self.report, api.capture(self.root))
                if failure == 'unlink-failed':
                    self.assertIn('injected base unlink failure', result['base_maintenance']['detail'])
                    self.assertIsNone(api.read_seed_base(self.root))
                else:
                    self.assertFalse(path.exists(), '[FAIL] canonical_reuse_invalidates_untrusted_base')

    def test_prepare_tolerates_only_already_unknown_base_unlink_failure(self):
        api = self.dev_repository()
        path = self.root / api.BASE_RECORD
        unlink = Path.unlink
        def remove(source, *args, **kwargs):
            if source == path:
                raise OSError('injected base unlink failure')
            return unlink(source, *args, **kwargs)
        with patch.object(Path, 'unlink', remove):
            with self.assertRaises(OSError, msg='[FAIL] trusted_base_invalidation_remains_required'):
                api.prepare(self.root, self.report)
            self.assertTrue(publication.member(self.report, api.SUFFIX).is_file())
            path.write_text('{invalid')
            try:
                result = api.prepare(self.root, self.report)
            except OSError as error:
                self.fail('[FAIL] unknown_base_maintenance_does_not_block_prepare: ' + str(error))
        self.assertIn('injected base unlink failure', result['detail'])
        self.assertIsNone(api.read_seed_base(self.root))
        self.assertFalse(publication.member(self.report, api.SUFFIX).exists())

    def test_failure_cleanup_removes_only_the_observed_receipt(self):
        api = self.dev_repository()
        snapshot = self.root / '.lake/cleanup-receipt'
        try:
            api.reuse(self.root, self.report, self.report, receipt_snapshot=snapshot)
        except TypeError as error:
            self.fail('[FAIL] reuse_captures_cleanup_generation_under_guard: ' + str(error))
        receipt = publication.member(self.report, api.SUFFIX)
        observed = receipt.read_bytes()
        base = (self.root / api.BASE_RECORD).read_bytes()
        try:
            api.invalidate_receipt(self.root, self.report, snapshot)
        except TypeError as error:
            self.fail('[FAIL] failure_cleanup_requires_observed_generation: ' + str(error))
        self.assertFalse(receipt.exists(), '[FAIL] cleanup_invalidates_its_own_failed_receipt')
        receipt.write_bytes(observed)
        changed = json.loads(observed)
        changed['completed'] = ['defaults']
        receipt.write_bytes(materials.canonical_json(changed))
        competing = receipt.read_bytes()
        api.invalidate_receipt(self.root, self.report, snapshot)
        self.assertTrue(receipt.exists(), '[FAIL] cleanup_preserves_a_different_receipt')
        self.assertEqual(competing, receipt.read_bytes())
        self.assertEqual(base, (self.root / api.BASE_RECORD).read_bytes())
        snapshot.unlink()
        api.invalidate_receipt(self.root, self.report, snapshot)
        self.assertEqual(competing, receipt.read_bytes(), '[FAIL] no_observed_receipt_means_no_cleanup')

    def test_cleanup_snapshot_write_failure_preserves_accepted_receipt(self):
        api = self.dev_repository()
        snapshot = self.root / '.lake/cleanup-directory'
        snapshot.mkdir()
        with self.assertRaises(OSError, msg='[FAIL] snapshot_writer_error_stays_outside_seed_rejection'):
            api.reuse(self.root, self.report, self.report, receipt_snapshot=snapshot)
        self.assertFalse(api.probe(self.root, self.report)['needs_lake'],
                         '[FAIL] snapshot_writer_error_preserves_accepted_receipt')
        self.assertTrue(api.seed_format(self.report)['compatible'])
        self.assertIsNotNone(api.read_seed_base(self.root))

    def test_initial_receipt_observation_is_guarded_and_preparation_clears_it(self):
        api = self.dev_repository()
        snapshot = self.root / '.lake/observed-receipt'
        receipt = publication.member(self.report, api.SUFFIX)
        before_receipt = receipt.read_bytes()
        before_base = (self.root / api.BASE_RECORD).read_bytes()
        sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
        from lean_cache_release import cache_guard
        try:
            with cache_guard(self.root):
                with self.assertRaises(BlockingIOError, msg='[FAIL] observation_requires_existing_guard'):
                    api.observe_receipt(self.root, self.report, snapshot)
        except AttributeError as error:
            self.fail('[FAIL] initial_receipt_has_generation_scoped_cleanup: ' + str(error))
        self.assertFalse(snapshot.exists())
        api.observe_receipt(self.root, self.report, snapshot)
        self.assertEqual(before_receipt, receipt.read_bytes())
        self.assertEqual(before_base, (self.root / api.BASE_RECORD).read_bytes())
        self.assertEqual(publication.digest(receipt), snapshot.read_text().strip())
        api.prepare(self.root, self.report, receipt_snapshot=snapshot)
        self.assertFalse(snapshot.exists(), '[FAIL] preparation_skips_redundant_cleanup')
        self.assertFalse(receipt.exists())

    def test_custom_source_reuse_does_not_inherit_canonical_producer(self):
        api = self.dev_repository()
        canonical, base = self.report, api.read_seed_base(self.root)
        original = api.seed_identity(canonical)
        self.write('D5/A.lean', 'def a := 2\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean'], check=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Fixture',
                        '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                        'commit', '-qm', 'new custom report inputs'], check=True)
        self.report = self.output
        self.report.parent.mkdir(parents=True, exist_ok=True)
        self.receipt()
        self.assertEqual(base, api.read_seed_base(self.root))
        self.assertFalse(api.reuse(self.root, self.report, canonical)['needs_lake'])
        self.assertNotEqual(original, api.seed_identity(canonical))
        self.assertIsNone(api.read_seed_base(self.root),
                          '[FAIL] custom_source_cannot_inherit_canonical_producer')
        self.assertFalse((self.root / api.BASE_RECORD).exists())
        self.assertFalse(api.probe(self.root, canonical)['needs_lake'])

    def dev_repository(self):
        self.write('.gitignore', '.lake/\nseed/\noutput/\n')
        self.report = self.root / '.lake/build/stratalint' / publication.RAW
        self.report.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git', 'init', '-q', '-b', 'dev', str(self.root)], check=True, capture_output=True)
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5', 'lean-toolchain', 'lakefile.toml',
                        '.gitignore', 'Audit.lean', 'Inspector.lean', 'producer.py', 'tools',
                        'bin', 'lean-report-inputs.json', 'lake-manifest.json'],
                       check=True, capture_output=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Fixture',
                        '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                        'commit', '-qm', 'base fixture'], check=True, capture_output=True)
        return self.receipt()

    def test_untracked_file_prevents_trusted_seed_base(self):
        api = self.dev_repository()
        self.assertIsNotNone(api.read_seed_base(self.root))
        self.write('untracked.txt', 'extra input\n')
        self.receipt()
        self.assertIsNone(api.read_seed_base(self.root), '[FAIL] untracked_file_has_unknown_base')
        self.assertFalse((self.root / api.BASE_RECORD).exists())
        self.assertTrue(api.seed_format(self.report)['compatible'])

    def test_untracked_registered_lean_source_prevents_trusted_seed_base(self):
        api = self.dev_repository()
        self.write('D5/Untracked.lean', 'def extra := 2\n')
        self.assertIn('D5/Untracked.lean', api.capture(self.root)['files'])
        self.receipt()
        self.assertIsNone(api.read_seed_base(self.root), '[FAIL] untracked_lean_has_unknown_base')
        self.assertFalse((self.root / api.BASE_RECORD).exists())
        self.assertTrue(api.seed_format(self.report)['compatible'])

    def test_seed_identity_mismatch_is_unknown(self):
        api = self.dev_repository()
        record = self.root / api.BASE_RECORD
        contents = json.loads(record.read_text())
        contents['seed_sha256'] = 'f' * 64
        record.write_text(json.dumps(contents))
        self.assertIsNone(api.read_seed_base(self.root), '[FAIL] different_seed_identity_is_unknown')
        self.assertFalse(api.probe(self.root, self.report)['needs_lake'])
        self.assertTrue(api.seed_format(self.report)['compatible'])

    def test_base_identity_covers_every_sidecar_and_receipt(self):
        api = self.dev_repository()
        base = api.read_seed_base(self.root)
        self.assertIsNotNone(base)
        for suffix in (*publication.SUFFIXES, api.SUFFIX):
            with self.subTest(suffix=suffix):
                path = publication.member(self.report, suffix)
                original = path.read_bytes()
                try:
                    path.write_bytes(original + b'\n')
                    self.assertIsNone(api.read_seed_base(self.root),
                                      '[FAIL] complete_seed_identity_binds_member_' + suffix)
                finally:
                    path.write_bytes(original)
                self.assertEqual(base, api.read_seed_base(self.root))

    def test_dirty_production_invalidates_previous_base(self):
        api = self.dev_repository()
        self.assertIsNotNone(api.read_seed_base(self.root))
        self.write('D5/A.lean', 'def a := 2\n')
        self.receipt()
        self.assertFalse((self.root / api.BASE_RECORD).exists(), '[FAIL] dirty_production_removes_old_base')
        self.assertTrue(api.seed_format(self.report)['compatible'])

    def test_failed_base_write_invalidates_previous_base(self):
        api = self.dev_repository()
        with patch.object(api.os, 'replace', side_effect=OSError('injected base write failure')):
            recorded = api.record_seed_base(self.root)
        self.assertFalse(recorded)
        self.assertFalse((self.root / api.BASE_RECORD).exists(), '[FAIL] failed_base_write_removes_old_base')

    def test_non_dev_detached_and_linked_seed_records_are_invalidated(self):
        api = self.dev_repository()
        path = self.root / api.BASE_RECORD
        record = path.read_bytes()
        for scope in ('non-dev', 'detached', 'linked'):
            with self.subTest(scope=scope):
                repository = self.root
                if scope == 'non-dev':
                    subprocess.run(['git', '-C', str(self.root), 'branch', '-M', 'topic'], check=True)
                elif scope == 'detached':
                    subprocess.run(['git', '-C', str(self.root), 'checkout', '-q', '--detach'], check=True)
                else:
                    repository = self.root / 'linked'
                    subprocess.run(['git', '-C', str(self.root), 'worktree', 'add', '-q', '-b', 'dev',
                                    str(repository), 'HEAD'], check=True)
                target = repository / api.BASE_RECORD
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(record)
                self.assertFalse(api.record_seed_base(repository))
                self.assertFalse(target.exists(), '[FAIL] untrusted_production_removes_old_base')

    def test_non_object_base_record_is_unknown(self):
        api = self.receipt()
        path = self.root / api.BASE_RECORD
        path.parent.mkdir(parents=True, exist_ok=True)
        for value in ([], None, 42, 'commit'):
            with self.subTest(value=value):
                path.write_text(json.dumps(value))
                try:
                    base = api.read_seed_base(self.root)
                except AttributeError as error:
                    self.fail('[FAIL] non_object_base_is_unknown: ' + str(error))
                self.assertIsNone(base)

    def test_seal_and_base_write_share_cache_guard(self):
        api = self.dev_repository()
        sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
        from lean_cache_release import cache_guard
        base = (self.root / api.BASE_RECORD).read_bytes()
        receipt = publication.member(self.report, api.SUFFIX).read_bytes()
        with cache_guard(self.root):
            with self.assertRaises(BlockingIOError, msg='[FAIL] seal_requires_exclusive_cache_ownership'):
                api.seal(self.root, self.report, api.capture(self.root), publication.bundle_identity(self.report))
        self.assertEqual(base, (self.root / api.BASE_RECORD).read_bytes())
        self.assertEqual(receipt, publication.member(self.report, api.SUFFIX).read_bytes())

    def test_standalone_program_entry_builds_the_producer_once_before_ensure(self):
        process, calls = self.entry_with_program_build(['leanInspector/LeanInformationAudit'], prebuilt=False)
        self.assertNotIn('bad-producer-build-args', calls, '[FAIL] producer_build_uses_target_path_contract')
        self.assertEqual(process.returncode, 0, process.stdout + process.stderr)
        self.assertEqual(calls[:2], ['producer-build', 'ensure'], '[FAIL] standalone_entry_builds_producer_before_ensure')
        self.assertEqual(len(calls), 3)
        self.assertTrue(calls[2].endswith(' build leanInspector/LeanInformationAudit'))
        self.assertEqual((self.root / 'ensure-producer').read_text(), 'producer.dll\n',
                         '[FAIL] ensure_runs_the_built_producer')

    def test_standalone_entry_fails_when_the_producer_build_reports_no_usable_dll(self):
        for case in ['no output', 'relative path', 'absent absolute path']:
            with self.subTest(case=case):
                # Each case starts from a fresh cold fixture.
                self.setUp()
                stdout = {'no output': '', 'relative path': 'producer.dll\n',
                          'absent absolute path': f'{self.root}/absent/producer.dll\n'}[case]
                process, calls = self.entry_with_program_build(
                    ['leanInspector/LeanInformationAudit'], prebuilt=False, producer_stdout=stdout)
                self.assertEqual(process.returncode, 2, '[FAIL] pathless_producer_build_fails_entry: '
                                 + process.stdout + process.stderr)
                self.assertIn('the producer build reported no existing absolute DLL', process.stderr,
                              '[FAIL] pathless_producer_build_names_the_defect')
                self.assertEqual(calls, ['producer-build'], '[FAIL] pathless_producer_build_runs_no_later_step')

    def test_probe_cli_reports_misses_but_rejects_invalid_registration(self):
        self.receipt()
        command = [sys.executable, '-B', str(HERE / 'reuse.py'), 'probe', '--repository', str(self.root),
                   '--report', str(self.report)]
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
        for path in ['D5/A.lean', 'lean-toolchain', 'lakefile.toml']:
            with self.subTest(changed=path):
                source = self.root / path
                original, stamp = source.read_bytes(), source.stat()
                source.write_bytes(original + b'\n')
                os.utime(source, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
                self.assertTrue(api.probe(self.root, self.report)['needs_lake'])
                source.write_bytes(original)
        self.write('D5/New.lean', 'def fresh := 2\n')
        self.assertTrue(api.probe(self.root, self.report)['needs_lake'])

        api = self.receipt()
        (self.root / 'D5/New.lean').unlink()
        self.assertTrue(api.probe(self.root, self.report)['needs_lake'])
        api = self.receipt()
        for name in EXECUTION['environment']:
            with self.subTest(environment=name), patch.dict(os.environ, {name: 'changed'}):
                self.assertTrue(api.probe(self.root, self.report)['needs_lake'])
        with patch.object(api.platform, 'machine', return_value='another-architecture'):
            self.assertTrue(api.probe(self.root, self.report)['needs_lake'])

    def test_mismatch_explains_input_changes_without_exposing_environment(self):
        self.write('D5/Removed.lean', 'def removed := 1\n')
        api = self.receipt()
        self.write('D5/A.lean', 'def a := 2\n')
        self.write('D5/Added.lean', 'def added := 1\n')
        (self.root / 'D5/Removed.lean').unlink()
        with patch.dict(os.environ, ELAN_TOOLCHAIN='private-toolchain-value'):
            result = api.probe(self.root, self.report)
        self.assertTrue(result['needs_lake'])
        self.assertEqual(result['mismatch'], dict(added_inputs=1, removed_inputs=1, changed_inputs=1, execution_changed=True))
        output = io.StringIO()
        with patch.dict(os.environ, GITHUB_ACTIONS='true'):
            api.warn_mismatch(result, output)
        warning = output.getvalue()
        self.assertTrue(warning.startswith('::warning title=Lean report cache mismatch::'))
        self.assertIn('Lake determines the module work from compiler traces', warning)
        self.assertIn('LEAN_CACHE and LEAN_INSPECTOR_WORK', warning)
        self.assertNotIn('private-toolchain-value', json.dumps(result) + warning)

    def test_mismatch_cli_preserves_json_probe_and_surfaces_reuse_warning(self):
        self.receipt()
        self.write('D5/A.lean', 'def a := 2\n')
        args = ['--repository', str(self.root), '--report', str(self.report)]
        with patch.dict(os.environ, GITHUB_ACTIONS='true'):
            probe = subprocess.run([sys.executable, '-B', str(HERE / 'reuse.py'), 'probe',
                *args, '--diagnostics'], text=True, capture_output=True, check=False)
            reuse = subprocess.run([sys.executable, '-B', str(HERE / 'reuse.py'), 'reuse',
                *args, '--output', str(self.output)], text=True, capture_output=True, check=False)
        self.assertEqual(probe.returncode, 0, probe.stderr)
        self.assertTrue(json.loads(probe.stdout)['needs_lake'])
        self.assertIn('::warning title=Lean report cache mismatch::', probe.stderr)
        self.assertIn('Lake determines the module work from compiler traces', probe.stderr)
        self.assertNotIn('Previous-version module reports are incompatible', probe.stderr)
        self.assertEqual(reuse.returncode, 3, reuse.stderr)
        self.assertIn('::warning title=Lean report cache mismatch::', reuse.stdout)
        self.assertFalse(self.output.exists())

    def test_hits_and_unavailable_receipts_do_not_claim_input_mismatch(self):
        api = self.receipt()
        output = io.StringIO()
        api.warn_mismatch(api.probe(self.root, self.report), output)
        receipt = publication.member(self.report, '.reuse.json')
        record = json.loads(receipt.read_text())
        for invalid in [None, [], {'files': None}]:
            record['inputs'] = invalid
            receipt.write_text(json.dumps(record))
            result = api.probe(self.root, self.report)
            self.assertTrue(result['needs_lake'])
            api.warn_mismatch(result, output)
        receipt.unlink()
        api.warn_mismatch(api.probe(self.root, self.report), output)
        self.assertEqual(output.getvalue(), '')

    def test_registered_file_executable_bit_changes_invalidate_reuse_and_sealing(self):
        api = self.receipt()
        captured = api.capture(self.root)
        source = self.root / 'D5/A.lean'
        source.chmod(0o755)
        self.assertTrue(api.probe(self.root, self.report)['needs_lake'],
                        '[FAIL] report_module_mode_change_invalidates_reuse')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            api.seal(self.root, self.report, captured, publication.bundle_identity(self.report))

    def test_checkout_permission_differences_keep_reuse(self):
        # Two checkouts of one commit may differ in permission bits other than
        # the owner executable bit Git records; the report is unchanged.
        paths = ('D5/A.lean', 'lean-toolchain', 'lakefile.toml')
        for path in paths:
            (self.root / path).chmod(0o644)
        api = self.receipt()
        for path, changed in ((path, mode) for path in paths for mode in (0o600, 0o654)):
            source = self.root / path
            with self.subTest(path=path, mode=oct(changed)):
                source.chmod(changed)
                try:
                    self.assertEqual(api.probe(self.root, self.report),
                                     dict(needs_lake=False, reason='receipt-matched'),
                                     '[FAIL] checkout_permission_difference_keeps_reuse')
                finally:
                    source.chmod(0o644)

    def test_producer_program_bytes_never_gate_reuse(self):
        api = self.receipt()
        captured = api.capture(self.root)
        producer_only = ['producer.py', 'tools/scripts/report/lean-report-selection.py',
                         'Inspector.lean', 'Audit.lean']
        self.assertEqual(set(captured['files']), {'D5/A.lean', 'lean-toolchain', 'lakefile.toml'},
                         '[FAIL] receipt_population_is_report_modules_and_configuration_only')
        self.assertFalse(set(producer_only + ['lean-report-inputs.json']) & set(captured['files']),
                         '[FAIL] producer_program_not_hashed')
        for path in producer_only:
            with self.subTest(changed=path):
                source = self.root / path
                original, mode = source.read_bytes(), source.stat().st_mode
                source.write_bytes(original + b'\n# producer-only edit\n')
                source.chmod(0o700)
                self.assertEqual(api.probe(self.root, self.report),
                                 dict(needs_lake=False, reason='receipt-matched'),
                                 '[FAIL] producer_program_change_keeps_receipt')
                source.write_bytes(original)
                source.chmod(mode)
        # Report format changes invalidate an otherwise unchanged receipt.
        with patch.object(publication.selection, 'REPORT_FORMAT', 'stratalint-report-next-format'):
            result = api.probe(self.root, self.report)
            self.assertTrue(result['needs_lake'], '[FAIL] report_format_invalidates_receipt')

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
                    self.assertTrue(api.probe(self.root, self.report)['needs_lake'])
                    self.assertTrue(api.reuse(self.root, self.report, self.output)['needs_lake'])
                    path.unlink(missing_ok=True)
                    path.write_bytes(original)
        receipt = publication.member(self.report, '.reuse.json')
        record = json.loads(receipt.read_text())
        record['completed'] = ['report', 'publication']
        receipt.write_text(json.dumps(record))
        self.assertTrue(api.probe(self.root, self.report)['needs_lake'])

    def test_validation_uses_material_reader_and_private_publication(self):
        api = self.receipt()
        validator = publication.validate_bundle
        def mutate_private(report, *args, **kwargs):
            result = validator(report, *args, **kwargs)
            if '.lean-report.' in str(report):
                publication.member(report, '.materials.zip').write_bytes(b'changed during validation')
            return result
        with patch.object(publication, 'validate_bundle', side_effect=mutate_private):
            self.assertTrue(api.reuse(self.root, self.report, self.output)['needs_lake'])
        self.assertFalse(self.output.exists())
        # Like a restored olean, sealed bytes are reused without replaying row validation.
        with patch.object(publication, 'validate_rows', wraps=publication.validate_rows) as rows:
            self.assertFalse(api.reuse(self.root, self.report, self.output)['needs_lake'])
            self.assertEqual(rows.call_count, 0, '[FAIL] sealed_bundle_rows_not_revalidated')
        self.assertTrue(self.output.exists())

    def test_optional_decoder_damage_is_a_miss_but_programming_errors_escape(self):
        api = self.receipt()
        errors = [zlib.error('broken DEFLATE seed'), NotImplementedError('unsupported ZIP method')]
        if zipfile.lzma is not None:
            errors.append(zipfile.lzma.LZMAError('broken LZMA seed'))
        for error in errors:
            with self.subTest(error=type(error).__name__), patch.object(
                    publication, 'validate_bundle', side_effect=error):
                try:
                    self.assertFalse(api.probe(self.root, self.report)['needs_lake'])
                    self.assertTrue(api.reuse(self.root, self.report, self.output)['needs_lake'])
                except type(error):
                    self.fail('[FAIL] optional_decoder_error_must_request_lake')
        with patch.object(publication, 'validate_bundle', side_effect=AssertionError('programming error')):
            self.assertFalse(api.probe(self.root, self.report)['needs_lake'])
            with self.assertRaisesRegex(AssertionError, 'programming error'):
                api.reuse(self.root, self.report, self.output)

    def test_semantic_seed_miss_preserves_absent_destination_parents(self):
        api = self.receipt()
        # The receipt matches, but the sealed envelope is invalid.
        sidecar = publication.member(self.report, '.sha256')
        sidecar.write_text('0' * 64 + '  ' + self.report.name + '\n')
        receipt = publication.member(self.report, '.reuse.json')
        record = json.loads(receipt.read_text())
        record['bundle']['.sha256'] = publication.digest(sidecar)
        receipt.write_text(json.dumps(record))
        output = self.root / '.lake/build/stratalint' / publication.RAW
        self.assertTrue(api.reuse(self.root, self.report, output)['needs_lake'])
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
            self.assertTrue(api.reuse(self.root, self.report, self.report)['needs_lake'])
        self.assertFalse(publication.member(self.report, '.reuse.json').exists())

    def test_seal_and_reuse_reject_input_changes_during_work(self):
        api = self.receipt()
        captured = api.capture(self.root)
        self.write('D5/A.lean', 'def a := 2\n')
        with self.assertRaisesRegex(ValueError, 'inputs changed'):
            api.seal(self.root, self.report, captured, publication.bundle_identity(self.report))
        self.write('D5/A.lean', 'def a := 1\n')
        api = self.receipt()
        publish = publication.publish
        def mutate_after_publish(*args, **kwargs):
            publish(*args, **kwargs)
            self.write('D5/A.lean', 'def a := 3\n')
        with patch.object(publication, 'publish', side_effect=mutate_after_publish):
            self.assertTrue(api.reuse(self.root, self.report, self.output)['needs_lake'])
        self.assertFalse(publication.member(self.output, '.reuse.json').exists())

    def test_missing_execution_contract_disables_only_reuse(self):
        api = self.receipt()
        del self.policy['report_execution']
        self.write_policy()
        captured = api.capture(self.root)
        self.assertTrue(api.probe(self.root, self.report)['needs_lake'])
        api.seal(self.root, self.report, captured, publication.bundle_identity(self.report))
        self.assertFalse(publication.member(self.report, '.reuse.json').exists())
        self.policy['report_execution'] = dict(EXECUTION, tools=['arbitrary-command'])
        self.write_policy()
        with self.assertRaisesRegex(ValueError, 'report_execution'):
            api.probe(self.root, self.report)
        with self.assertRaisesRegex(ValueError, 'report_execution'):
            api.reuse(self.root, self.report, self.output)

    def entry_with_program_build(self, targets, *, seed=True, build_exit=0,
                                 existing_output=False, registered_targets=('FixtureAudit',), prebuilt=True,
                                 producer_stdout=None):
        # Exercise the actual shell entry and report receipt, replacing only the
        # external cache/build processes. No Lean compilation is needed here.
        for relative in ('tools/lean-inspector/inspect.sh', 'tools/lean-inspector/reuse.py',
                         'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                         'tools/lean-inspector/build_work.py', 'tools/scripts/lib/resource-observation-lib.sh',
                         'tools/scripts/worktree/lean_cache_release.py',
                         'tools/scripts/worktree/lean_cache.py', 'tools/scripts/worktree/cache_material.py'):
            target = self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / relative, target)
        ensure = self.root / 'tools/scripts/worktree/lean-cache-ensure.sh'
        ensure.write_text('#!/bin/bash\nset -euo pipefail\n'
                          + ('' if existing_output else 'test ! -e .lake\n')
                          + 'printf "ensure\\n" >> build-calls\nmkdir -p .lake\n'
                          + 'printf "%s\\n" "${STRATALINT_LEAN_PRODUCER_DLL##*/}" >> ensure-producer\n')
        runner = self.root / 'tools/scripts/worktree/lean-cache-run.sh'
        runner.write_text('#!/bin/bash\nset -euo pipefail\n'
                          'printf "%s\\n" "$*" >> build-calls\n'
                          'exit ' + str(build_exit) + '\n')
        runner.chmod(0o755)
        api = self.receipt()
        self.output = self.root / '.lake/build/stratalint' / publication.RAW
        if existing_output:
            self.assertFalse(api.reuse(self.root, self.report, self.output)['needs_lake'])
            self.assertTrue(publication.member(self.output, '.reuse.json').is_file())
        if not seed:
            publication.member(self.report, '.reuse.json').unlink()
        elif seed == 'corrupt':
            publication.member(self.report, '.reuse.json').write_text('damaged receipt')
        self.seed_before = {path: path.read_bytes() for path in self.report.parent.iterdir()}
        producer = self.root / 'producer.dll'
        producer.write_text('fixture executable')
        environment = dict(os.environ, LAKE_BIN=str(self.lake),
            STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_PRODUCER_DLL=str(producer),
            STRATALINT_LEAN_REPORT_REUSE=str(self.report),
            STRATALINT_LEAN_BUILD_TARGETS=targets if isinstance(targets, str) else json.dumps(targets))
        if not prebuilt:
            # A standalone entry builds the producer and reports its DLL, unless the
            # test substitutes the build's whole standard output. The stub answers
            # only the entry's contract: the csproj's own TargetPath.
            dotnet = self.root / 'dotnet-bin/dotnet'
            dotnet.parent.mkdir()
            dotnet.write_text('#!/bin/sh\n'
                              'bad() { printf "bad-producer-build-args\\n" >> build-calls; exit 64; }\n'
                              '[ "$1" = build ] || bad\n'
                              'for required in " --configuration Release " " -t:Build " " -getProperty:TargetPath " '
                              '"/StrataLint.Lean/StrataLint.Lean.csproj "; do\n'
                              '  case " $* " in *"$required"*) ;; *) bad ;; esac\n'
                              'done\n'
                              'printf "producer-build\\n" >> build-calls\n'
                              + ('printf "%s\\n" "$PWD/producer.dll"\n' if producer_stdout is None
                                 else 'printf %s ' + shlex.quote(producer_stdout) + '\n'))
            dotnet.chmod(0o755)
            environment.pop('STRATALINT_LEAN_PRODUCER_DLL')
            environment['PATH'] = str(dotnet.parent) + os.pathsep + environment['PATH']
        if existing_output and seed == 'valid':
            environment.pop('STRATALINT_LEAN_REPORT_REUSE')
        if targets is None:
            environment.pop('STRATALINT_LEAN_BUILD_TARGETS')
        result = subprocess.run(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(self.output),
            '--log-dir', str(self.root / 'logs')], env=environment, text=True, capture_output=True)
        calls = self.root / 'build-calls'
        return result, calls.read_text().splitlines() if calls.exists() else []





if __name__ == '__main__':
    unittest.main()
