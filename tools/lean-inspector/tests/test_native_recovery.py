"""Execute native Lake facets in private pinned-toolchain fixture packages."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from unittest.mock import patch
import zipfile

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
ROOT = Path(os.environ.get('STRATALINT_NATIVE_SOURCE_ROOT', ROOT)).resolve()
sys.path.insert(0, str(HERE))
import publication
import materials
import native



from test_native_support import *


class NativeBatchPartitionTests:
    def test_partition_preserves_membership_and_order(self):
        requests = [['/root', f'Module.{index:03}', '', '', '/inspector', '']
                    for index in range(201, -1, -1)]
        chunks = []
        with patch.object(native, 'produce_batch_chunk', side_effect=chunks.append):
            native.produce_batch(requests)
        self.assertEqual([len(chunk) for chunk in chunks], [100, 100, 2])
        self.assertEqual([row[1] for chunk in chunks for row in chunk],
                         [f'Module.{index:03}' for index in range(202)])

    def test_partition_binds_reg_sized_inventory(self):
        requests = [['/root', f'Reg.Module.{index:03}', '', '', '/inspector', '']
                    for index in range(97)]
        chunks = []
        with patch.object(native, 'produce_batch_chunk', side_effect=chunks.append):
            native.produce_batch(requests)
        self.assertEqual([len(chunk) for chunk in chunks], [97])

    def test_partition_rejects_cross_chunk_duplicate_and_mixed_owner(self):
        requests = [['/root', f'Module.{index:03}', '', '', '/inspector', '']
                    for index in range(101)]
        for replacement, diagnostic in [
            (['/root', 'Module.099', '', '', '/inspector', ''], 'duplicate native batch module'),
            (['/other', 'Module.101', '', '', '/inspector', ''], 'mixed native batch owners'),
        ]:
            with self.subTest(diagnostic=diagnostic), \
                    patch.object(native, 'produce_batch_chunk') as chunk:
                with self.assertRaisesRegex(ValueError, diagnostic):
                    native.produce_batch(requests + [replacement])
                chunk.assert_not_called()


class NativeRecoveryConsumerTests:
    def test_release_stage_and_verify_preserve_absent_lake(self):
        self.build()
        self.publish()
        incoming = self.root / 'public.json'
        with tempfile.TemporaryDirectory(prefix='inspector-release.') as directory:
            directory = Path(directory)
            temporary = directory / 'tmp'
            temporary.mkdir()
            for damage in ['none', 'missing', 'stale', 'changed-dependency']:
                with self.subTest(damage=damage):
                    root = directory / damage
                    shutil.copytree(self.root, root, ignore=shutil.ignore_patterns('.lake', '.git'))
                    subprocess.run(['git', 'init', '--quiet', str(root)], check=True,
                        capture_output=True, timeout=120)
                    bundle = incoming if damage != 'missing' else directory / 'absent.json'
                    if damage == 'stale':
                        source = root / 'D5/Alone.lean'
                        source.write_text(source.read_text() + '-- changed input\n')
                    elif damage == 'changed-dependency':
                        (root / 'ClaimSupport.lean').write_text('def claimSupport : Prop := True\n')
                    environment = dict(self.env, TMPDIR=str(temporary),
                        STRATALINT_LEAN_INPUT_MEMO_ROOT=str(directory / 'verify-memo'))
                    staged = directory / ('staged-' + damage) / publication.RAW
                    stage = subprocess.run([sys.executable, '-B', str(root / 'tools/lean-inspector/publication.py'),
                        'stage', '--bundle', str(bundle), '--staging-directory', str(staged.parent),
                        '--repository', str(root)], cwd=directory, env=environment,
                        text=True, capture_output=True, timeout=120)
                    accepted = damage in ['none', 'changed-dependency']
                    self.assertEqual(stage.returncode, 0 if accepted else 1, stage.stdout + stage.stderr)
                    self.assertFalse((root / '.lake').exists(), 'stage must preserve whole-tree donor eligibility')
                    self.assertEqual(list(temporary.iterdir()), [], 'stage must clean its input memo')
                    verify = subprocess.run(['bash', str(root / 'tools/scripts/report/lean-report-input.sh'),
                        'verify', '--repository', str(root), '--report', str(staged if accepted else bundle)],
                        cwd=directory, env=environment, text=True, capture_output=True, timeout=120)
                    self.assertEqual(verify.returncode,
                        {'none': 0, 'missing': 2, 'stale': 2, 'changed-dependency': 0}[damage], verify.stdout + verify.stderr)
                    if accepted:
                        self.assertEqual(staged.read_bytes(), incoming.read_bytes())
                        self.assertEqual(publication.member(staged, '.materials.zip').read_bytes(),
                            publication.member(incoming, '.materials.zip').read_bytes())
                    else:
                        self.assertFalse(staged.exists())
                        diagnostic = {'missing': 'missing bundle member', 'stale': 'stale input/provenance'}[damage]
                        self.assertIn(diagnostic, stage.stderr)
                    self.assertFalse((root / '.lake').exists(), 'verify must preserve whole-tree donor eligibility')
                    self.assertEqual(list(temporary.iterdir()), [])
                    self.record_result('release-' + damage, dict(stage_exit=stage.returncode,
                        verify_exit=verify.returncode, lake_absent=True, temporary_clean=True))




    def test_native_imports_without_lzma_and_batch_failures_propagate(self):
        self.build()
        request = self.root / 'requests.json'
        artifact = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        # A fresh interpreter without lzma must still import the real producer.
        control = subprocess.run([sys.executable, '-B', '-c',
            'import sys; sys.modules["lzma"] = None; sys.path.insert(0, sys.argv[1]); import native',
            str(self.root / 'tools/lean-inspector')],
            cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
        self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
        errors = [ValueError('required producer failure')]
        if zipfile.lzma is not None:
            errors.append(zipfile.lzma.LZMAError('required producer decoder failure'))
        for kind, owner in [('produce', 'produce_batch'), ('aggregate', 'aggregate')]:
            request.write_text(json.dumps([[kind, [str(self.root), str(artifact)]]]))
            for error in errors:
                with self.subTest(kind=kind, exception=type(error).__name__):
                    with patch.object(native, owner, side_effect=error):
                        with self.assertRaises(type(error)):
                            native.batch(request)
    def test_native_required_failures(self):
        self.build()
        self.write('Audit.lean', 'def audit : False := True.intro\n')
        self.build(success=False, targets=['Audit'])
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        self.write('D5/A.lean', 'def invalid : False := True.intro\n')
        self.build(success=False)
        self.write('D5/A.lean', 'import D5.B\ndef value : Nat := D5.hidden\n')
        self.write('utility.json', '{invalid')
        self.build(success=False)
        self.utility()
        original_policy = (self.root / 'lean-report-inputs.json').read_text()
        for invalid in ['{invalid', original_policy.replace('"schema_version": 1', '"schema_version": 9'),
                        original_policy.replace('"pattern": "tools/scripts/report/lean-report-selection.py"',
                                                '"pattern": "absent-required-producer.py"')]:
            self.write('lean-report-inputs.json', invalid)
            self.build(success=False)
        (self.root / 'lean-report-inputs.json').unlink()
        self.build(success=False)
        self.write('lean-report-inputs.json', original_policy)
        (self.root / 'External.lean').unlink()
        self.build(success=False)
        self.write('External.lean', 'import ClaimSupport\ndef claim : Prop := claimSupport\n')
        self.utility()
        inspector = self.root / 'tools/lean-inspector/Inspector.lean'
        inspector.write_text(inspector.read_text() + '\ndef invalidProducer : False := True.intro\n')
        self.build(success=False)
        self.copy('tools/lean-inspector/Inspector.lean')
        (self.root / 'tools/lean-inspector/materials.py').unlink()
        self.build(success=False)


class NativeModuleFacetTests:
    def test_public_module_report_and_private_job_is_not_a_target(self):
        self.build()
        path = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        source = self.root / 'D5/Alone.lean'
        before = self.stamps()
        source.write_text(source.read_text() + '-- public module facet miss\n')
        self.write('activity.jsonl', '')
        self.run_lake('build', 'D5.Alone:report')
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.Alone'})
        self.assertEqual([json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()],
                         [dict(kind='extract', count=1)])
        result = self.run_lake('build', 'D5.Alone:inspectorModuleReport', success=False)
        self.assertIn('unknown module facet', result.stdout + result.stderr)
        for index, targets in enumerate([(':report', 'D5.Alone:report'), ('D5.Alone:report', ':report')]):
            with self.subTest(targets=targets):
                source.write_text(source.read_text() + f'-- shared miss {index}\n')
                self.write('activity.jsonl', '')
                self.run_lake('build', *targets)
                records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
                self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)
        self.assertTrue(path.is_file())

        # A required producer failure must fail both public module and package entrypoints.
        producer = self.root / 'tools/lean-inspector/native.py'
        producer.write_text(producer.read_text().replace(
            'def module(root, name, source, utility_path, executable, output):',
            'def module(root, name, source, utility_path, executable, output):\n'
            '    raise ValueError("required fixture producer failure")').replace(
            'def produce_batch(requests):',
            'def produce_batch(requests):\n    raise ValueError("required fixture producer failure")'))
        source.write_text(source.read_text() + '-- require module production\n')
        result = self.run_lake('build', 'D5.Alone:report', success=False)
        self.assertIn('required fixture producer failure', result.stdout + result.stderr)
        source.write_text(source.read_text() + '-- require a new native artifact\n')
        result = self.build(success=False)
        self.assertIn('required fixture producer failure', result.stdout + result.stderr)
