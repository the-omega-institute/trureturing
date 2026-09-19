"""Execute native Lake facets in private pinned-toolchain fixture packages."""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
import zipfile
import zlib

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
ROOT = Path(os.environ.get('STRATALINT_NATIVE_SOURCE_ROOT', ROOT)).resolve()
sys.path.insert(0, str(HERE))
import publication
import materials
import native



from test_native_support import *

class NativeRecoveryTests:
    def test_repaired_rows_share_one_validation_batch(self):
        commands = self.root / 'native-commands.jsonl'
        self.write('bin/python3', f'#!{sys.executable}\n'
            + 'import json, os, sys\nfrom pathlib import Path\n'
            + 'if len(sys.argv) > 2 and Path(sys.argv[1]).name == "native.py":\n'
            + '    row = {"arguments": sys.argv[2:]}\n'
            + '    if sys.argv[2] == "batch": row["requests"] = json.loads(Path(sys.argv[3]).read_text())\n'
            + f'    with Path({str(commands)!r}).open("a") as out: out.write(json.dumps(row) + "\\n")\n'
            + f'os.execv({sys.executable!r}, [{sys.executable!r}, *sys.argv[1:]])\n')
        (self.root / 'bin/python3').chmod(0o755)
        self.build()
        expected_report, expected_origins = self.report(), self.origins()
        modules = self.root / '.lake/build/lean-inspector/modules'
        expected = {path: path.read_bytes() for path in modules.glob('*.zip')}
        self.assertEqual(len(expected), 4)
        for path in expected:
            path.unlink()  # Never mutate a hard link into Lake's artifact cache.
            path.write_bytes(b'rejected optional module artifact')
        commands.write_text('')
        recovered = self.build()
        records = [json.loads(line) for line in commands.read_text().splitlines()]
        production = [index for index, row in enumerate(records)
                      if any(kind == 'produce' for kind, _ in row.get('requests', []))]
        self.assertEqual(len(production), 1)
        after_production = records[production[0] + 1:]
        standalone = [row for row in after_production if row['arguments'][:2] == ['validate', 'module']]
        batches = [row['requests'] for row in after_production if row['arguments'][0] == 'batch']
        validations = [[args for kind, args in batch if kind == 'validate' and args[1] == 'module']
                       for batch in batches]
        validations = [batch for batch in validations if batch]
        self.record_result('repaired-validation', dict(commands=records,
            standalone_module_validations=len(standalone), repaired_rows=len(expected),
            repaired_validation_batch_sizes=[len(batch) for batch in validations]), [commands])
        self.assertEqual(self.report(), expected_report)
        self.assertEqual(self.origins(), expected_origins)
        for path, content in expected.items():
            self.assertEqual(path.read_bytes(), content)
            self.assertEqual(path.stat().st_nlink, 1, 'reconstruction must remain private')
        self.assertEqual((recovered.stdout + recovered.stderr).count(
            'inspector artifact rejected; rebuilding privately'), len(expected))
        self.assertEqual(standalone, [], 'repaired modules must share the native validation invocation')
        self.assertEqual(len(validations), 1)
        self.assertEqual(len(validations[0]), len(expected))
        self.assertEqual({Path(args[-1]).resolve() for args in validations[0]},
                         {path.resolve() for path in expected})

    def test_repair_batch_rejects_invalid_reconstructed_material(self):
        producer = self.root / 'tools/lean-inspector/native.py'
        source = producer.read_text()
        target = '            produce_batch(produce)'
        self.assertEqual(source.count(target), 1)
        producer.write_text(source.replace(target, target + '\n'
            + '            for args in produce:\n'
            + '                if args[1] == "Fixture" and args[5].endswith(".repair"):\n'
            + '                    Path(args[5]).write_bytes(b"invalid reconstructed material")'))
        self.build()
        modules = self.root / '.lake/build/lean-inspector/modules'
        for path in modules.glob('*.zip'):
            path.unlink()
            path.write_bytes(b'rejected optional module artifact')
        rejected = self.build(success=False)
        self.assertIn('reconstructed Inspector artifact is invalid:', rejected.stdout + rejected.stderr)
        self.assertIn('modules/Fixture.zip', rejected.stdout + rejected.stderr)
        self.assertEqual((modules / 'Fixture.zip').read_bytes(), b'invalid reconstructed material')
        self.assertEqual(list(modules.glob('*.repair')), [])
        self.record_result('invalid-repair', dict(exit_code=rejected.returncode,
            output=rejected.stdout + rejected.stderr, invalid_module='Fixture'))

    def test_release_stage_and_verify_preserve_absent_lake(self):
        self.build()
        self.publish()
        incoming = self.root / 'public.json'
        with tempfile.TemporaryDirectory(prefix='inspector-release.') as directory:
            directory = Path(directory)
            temporary = directory / 'tmp'
            temporary.mkdir()
            for damage in ['none', 'missing', 'stale', 'stale-dependency']:
                with self.subTest(damage=damage):
                    root = directory / damage
                    shutil.copytree(self.root, root, ignore=shutil.ignore_patterns('.lake', '.git'))
                    subprocess.run(['git', 'init', '--quiet', str(root)], check=True,
                        capture_output=True, timeout=120)
                    bundle = incoming if damage != 'missing' else directory / 'absent.json'
                    if damage == 'stale':
                        source = root / 'D5/Alone.lean'
                        source.write_text(source.read_text() + '-- changed input\n')
                    elif damage == 'stale-dependency':
                        (root / 'ClaimSupport.lean').write_text('def claimSupport : Prop := True\n')
                    environment = dict(self.env, TMPDIR=str(temporary),
                        STRATALINT_LEAN_INPUT_MEMO_ROOT=str(directory / 'verify-memo'))
                    staged = directory / ('staged-' + damage) / publication.RAW
                    stage = subprocess.run([sys.executable, '-B', str(root / 'tools/lean-inspector/publication.py'),
                        'stage', '--bundle', str(bundle), '--staging-directory', str(staged.parent),
                        '--repository', str(root)], cwd=directory, env=environment,
                        text=True, capture_output=True, timeout=120)
                    self.assertEqual(stage.returncode, 0 if damage == 'none' else 1, stage.stdout + stage.stderr)
                    self.assertFalse((root / '.lake').exists(), 'stage must preserve whole-tree donor eligibility')
                    self.assertEqual(list(temporary.iterdir()), [], 'stage must clean its input memo')
                    verify = subprocess.run(['bash', str(root / 'tools/scripts/report/lean-report-input.sh'),
                        'verify', '--repository', str(root), '--report', str(staged if damage == 'none' else bundle)],
                        cwd=directory, env=environment, text=True, capture_output=True, timeout=120)
                    self.assertEqual(verify.returncode,
                        {'none': 0, 'missing': 2, 'stale': 2, 'stale-dependency': 1}[damage], verify.stdout + verify.stderr)
                    if damage == 'none':
                        self.assertEqual(staged.read_bytes(), incoming.read_bytes())
                        self.assertEqual(publication.member(staged, '.materials.zip').read_bytes(),
                            publication.member(incoming, '.materials.zip').read_bytes())
                    else:
                        self.assertFalse(staged.exists())
                        diagnostic = {'missing': 'missing bundle member', 'stale': 'stale input/provenance',
                                      'stale-dependency': 'stale dependency'}[damage]
                        self.assertIn(diagnostic, stage.stderr)
                    self.assertFalse((root / '.lake').exists(), 'verify must preserve whole-tree donor eligibility')
                    self.assertEqual(list(temporary.iterdir()), [])
                    self.record_result('release-' + damage, dict(stage_exit=stage.returncode,
                        verify_exit=verify.returncode, lake_absent=True, temporary_clean=True))

    def test_native_recovers_outer_member_without_lzma(self):
        self.check_missing_lzma_recovery(nested=False)

    def test_native_recovers_nested_material_without_lzma(self):
        self.check_missing_lzma_recovery(nested=True)

    def check_missing_lzma_recovery(self, *, nested):
        self.build()
        before, expected_report, origins = self.stamps(), self.report(), self.origins()
        path = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        expected = path.read_bytes()
        # Only child fixture interpreters lack LZMA; the host installation is
        # unchanged. Lake invokes the actual native.py with this explicit env.
        self.write('no-lzma/sitecustomize.py', 'import sys\nsys.modules["lzma"] = None\n')
        self.env['PYTHONPATH'] = str(self.root / 'no-lzma')
        request, statuses = self.root / 'requests.json', self.root / 'statuses.json'
        utility = self.root / '.lake/build/lean-inspector/inputs/D5.Alone.json'
        request.write_text(json.dumps([['validate', [str(self.root), 'module', str(self.root),
            'D5.Alone', str(utility), str(path)]]]))
        control = subprocess.run([sys.executable, '-B', '-c',
            'import sys, zipfile; assert zipfile.lzma is None; sys.path.insert(0, sys.argv[1]); '
            'import native; assert native.LZMA_ERRORS == (); native.batch(sys.argv[2], sys.argv[3])',
            str(self.root / 'tools/lean-inspector'), str(request), str(statuses)],
            env=self.env, cwd=self.root, text=True, capture_output=True, timeout=120)
        self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
        self.assertEqual(json.loads(statuses.read_text()), [0])

        def damage(data):
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                offset = archive.start_dir + 10
            changed = bytearray(data)
            struct.pack_into('<H', changed, offset, zipfile.ZIP_LZMA)
            return bytes(changed)

        if nested:
            output = io.BytesIO()
            with zipfile.ZipFile(io.BytesIO(expected)) as source, zipfile.ZipFile(output, 'w') as target:
                for info in source.infolist():
                    payload = source.read(info)
                    if info.filename.endswith('.materials.zip'):
                        # Repack as stored first: every CRC and member is valid
                        # before changing only the central compression method.
                        stored = io.BytesIO()
                        with zipfile.ZipFile(io.BytesIO(payload)) as inner, zipfile.ZipFile(stored, 'w') as dest:
                            for entry in inner.infolist():
                                dest.writestr(entry.filename, inner.read(entry), compress_type=zipfile.ZIP_STORED)
                        payload = damage(stored.getvalue())
                    target.writestr(info, payload)
            damaged = output.getvalue()
        else:
            damaged = damage(expected)
        path.unlink()
        path.write_bytes(damaged)
        probe = subprocess.run([sys.executable, '-B', '-c',
            'import io, json, sys, traceback, zipfile\n'
            'assert zipfile.lzma is None\n'
            'with zipfile.ZipFile(sys.argv[1]) as outer:\n'
            '    archive = zipfile.ZipFile(io.BytesIO(outer.read(sys.argv[2]))) if sys.argv[2] else outer\n'
            '    try: archive.read(archive.infolist()[0])\n'
            '    except RuntimeError as error:\n'
            '        assert str(error) == "Compression requires the (missing) lzma module"\n'
            '        print(json.dumps(dict(exception=type(error).__name__, message=str(error), '
            'frames=[frame.name for frame in traceback.extract_tb(error.__traceback__)])))\n'
            '    else: raise AssertionError("missing decoder was not reached")\n',
            str(path), publication.RAW + '.materials.zip' if nested else ''],
            env=self.env, cwd=self.root, text=True, capture_output=True, timeout=120)
        self.assertEqual(probe.returncode, 0, probe.stdout + probe.stderr)
        failure = json.loads(probe.stdout)
        self.assertIn('_get_decompressor', failure['frames'])
        self.record_result('decoder', dict(environment='child fixture blocks lzma import',
            host_lzma_available=zipfile.lzma is not None, valid_control_statuses=[0],
            nested=nested, **failure))
        self.write('activity.jsonl', '')
        stamp = (path.stat().st_ino, path.stat().st_mtime_ns)
        rejected = self.run_lake('--no-build', 'build', ':report', success=False)
        no_build = dict(exit_code=rejected.returncode, no_activity=(self.root / 'activity.jsonl').read_text() == '',
            artifact_unchanged=path.read_bytes() == damaged and stamp == (path.stat().st_ino, path.stat().st_mtime_ns),
            needs_rebuild='needs to be rebuilt' in rejected.stdout + rejected.stderr)
        self.record_result('no-build', no_build)
        self.assertTrue(no_build['no_activity'])
        self.assertTrue(no_build['artifact_unchanged'])
        recovered = self.build(success=None)
        self.record_result('recovery', dict(exit_code=recovered.returncode,
            output=recovered.stdout + recovered.stderr))
        self.assertEqual(recovered.returncode, 0, recovered.stdout + recovered.stderr)
        self.assertTrue(no_build['needs_rebuild'], rejected.stdout + rejected.stderr)
        self.assertIn('unavailable ZIP decoder: LZMA', recovered.stdout + recovered.stderr)
        self.assertEqual((recovered.stdout + recovered.stderr).count('inspector artifact rejected; rebuilding privately'), 1)
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.Alone'})
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)
        self.assertEqual(path.read_bytes(), expected)
        self.assertEqual(path.stat().st_nlink, 1)
        self.assertEqual(self.report(), expected_report)
        self.assertEqual(self.origins(), origins)
        self.publish()
        self.record_result('recovered', dict(activity=records, affected_rows=['D5.Alone'],
            exact_report_material_origins=True, private_links=path.stat().st_nlink))

    def test_native_recovers_only_row_with_damaged_deflate(self):
        def damage(data):
            with zipfile.ZipFile(io.BytesIO(data)) as outer:
                entries = [(info, outer.read(info)) for info in outer.infolist()]
            for index, (info, payload) in enumerate(entries):
                if info.filename.endswith('.materials.zip'):
                    damaged = bytearray(payload)
                    with zipfile.ZipFile(io.BytesIO(payload)) as nested:
                        entry = nested.infolist()[0]
                        self.assertEqual(entry.compress_type, zipfile.ZIP_DEFLATED)
                        offset = entry.header_offset
                    name_size, extra_size = struct.unpack_from('<HH', damaged, offset + 26)
                    offset += 30 + name_size + extra_size
                    # Reserved deflate block type, in an otherwise readable ZIP.
                    damaged[offset] = (damaged[offset] & ~6) | 6
                    entries[index] = (info, bytes(damaged))
            result = io.BytesIO()
            with zipfile.ZipFile(result, 'w') as outer:
                for info, payload in entries:
                    outer.writestr(info, payload)
            return result.getvalue()
        self.check_row_decoder_recovery(damage, zlib.error)
    def test_native_recovers_only_row_with_unsupported_compression(self):
        for method in [1, 2]:
            with self.subTest(method=method):
                def damage(data):
                    with zipfile.ZipFile(io.BytesIO(data)) as outer:
                        offset = outer.start_dir + 10
                    damaged = bytearray(data)
                    self.assertEqual(struct.unpack_from('<H', damaged, offset)[0], zipfile.ZIP_STORED)
                    damaged[offset] ^= method
                    return bytes(damaged)
                self.check_row_decoder_recovery(damage, NotImplementedError)
    @unittest.skipIf(zipfile.lzma is None, 'Python ZIP LZMA support is optional')
    def test_native_recovers_only_row_with_damaged_lzma(self):
        # Enough real report bytes for the LZMA decoder to reach the corrupt
        # properties, rather than stopping earlier on a truncated ZIP member.
        self.write('D5/Alone.lean', ''.join(
            f'theorem alone_{index} : True := True.intro\n' for index in range(256)))

        def damage(data):
            with zipfile.ZipFile(io.BytesIO(data)) as archive:
                self.assertEqual(archive.infolist()[0].filename, publication.RAW)
                offset = archive.start_dir + 10
            damaged = bytearray(data)
            self.assertEqual(struct.unpack_from('<H', damaged, offset)[0], zipfile.ZIP_STORED)
            struct.pack_into('<H', damaged, offset, zipfile.ZIP_LZMA)
            return bytes(damaged)

        self.check_row_decoder_recovery(damage, zipfile.lzma.LZMAError, no_build=True)
    def test_native_optional_lzma_and_batch_failure_boundaries(self):
        self.build()
        request = self.root / 'requests.json'
        result = self.root / 'statuses.json'
        artifact = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        utility = self.root / '.lake/build/lean-inspector/inputs/D5.Alone.json'
        validation = [str(self.root), 'module', str(self.root), 'D5.Alone', str(utility), str(artifact)]
        request.write_text(json.dumps([['validate', validation]]))
        # A fresh interpreter without lzma must still import the real producer
        # and validate the supported stored/deflated native artifact.
        control = subprocess.run([sys.executable, '-B', '-c',
            'import sys; sys.modules["lzma"] = None; sys.path.insert(0, sys.argv[1]); '
            'import native; native.batch(sys.argv[2], sys.argv[3])',
            str(self.root / 'tools/lean-inspector'), str(request), str(result)],
            cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
        self.assertEqual(control.returncode, 0, control.stdout + control.stderr)
        self.assertEqual(json.loads(result.read_text()), [0])
        result.unlink()
        with patch.object(native, 'validate', side_effect=RuntimeError('unrelated validator failure')):
            with self.assertRaisesRegex(RuntimeError, 'unrelated validator failure'):
                native.batch(request, result)
        self.assertFalse(result.exists())
        with patch.object(zipfile.ZipFile, 'open', side_effect=RuntimeError('unrelated ZIP read failure')):
            with self.assertRaisesRegex(RuntimeError, 'unrelated ZIP read failure'):
                native.batch(request, result)
        self.assertFalse(result.exists())
        errors = [ValueError('required producer failure')]
        if zipfile.lzma is not None:
            errors.append(zipfile.lzma.LZMAError('required producer decoder failure'))
        for kind, owner in [('produce', 'produce_batch'), ('aggregate', 'aggregate')]:
            request.write_text(json.dumps([[kind, [str(self.root), str(artifact)]]]))
            for error in errors:
                with self.subTest(kind=kind, exception=type(error).__name__):
                    with patch.object(native, owner, side_effect=error):
                        with self.assertRaises(type(error)):
                            native.batch(request, result)
                    self.assertFalse(result.exists())
        self.record_result('boundaries', dict(without_lzma_valid_control_exit=control.returncode,
            unrelated_validator_error_propagates=True, required_producer_errors_propagate=True,
            required_error_types=[type(error).__name__ for error in errors]))
    def test_native_recovers_only_row_with_encrypted_member(self):
        self.check_row_decoder_recovery(self.encrypted_member, ValueError)
    def test_native_recovers_only_row_with_encrypted_material(self):
        def damage(data):
            result = io.BytesIO()
            with zipfile.ZipFile(io.BytesIO(data)) as source, zipfile.ZipFile(result, 'w') as target:
                for info in source.infolist():
                    payload = source.read(info)
                    if info.filename.endswith('.materials.zip'):
                        payload = self.encrypted_member(payload)
                    target.writestr(info, payload)
            return result.getvalue()
        self.check_row_decoder_recovery(damage, ValueError)
    def test_native_recovers_encrypted_report(self):
        self.build()
        before = self.stamps()
        expected_report = self.report()
        origins = self.origins()
        path = self.root / '.lake/build/lean-inspector/report.zip'
        expected = path.read_bytes()
        damaged = self.encrypted_member(expected)
        path.unlink()
        path.write_bytes(damaged)
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            with self.assertRaisesRegex(ValueError, 'encrypted'):
                publication.unpack(path, directory)
        recovered = self.build()
        self.assertIn('inspector artifact rejected; rebuilding privately', recovered.stdout + recovered.stderr)
        self.assertEqual(self.stamps(), before)
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(records, [dict(kind='aggregate', count=1)])
        self.assertEqual(path.read_bytes(), expected)
        self.assertEqual(path.stat().st_nlink, 1, 'reconstruction must be private')
        self.assertEqual(self.report(), expected_report)
        self.assertEqual(self.origins(), origins)
    def test_native_recovery_and_required_failures(self):
        self.build()
        for artifact in ['modules/D5.Alone.zip', 'report.zip']:
            path = self.root / '.lake/build/lean-inspector' / artifact
            expected = path.read_bytes()
            # Replace, never edit a hard link into Lake's artifact cache.
            path.unlink()
            path.write_bytes(b'corrupt optional artifact')
            recovered = self.build()
            self.assertIn('inspector artifact rejected; rebuilding privately', recovered.stdout + recovered.stderr)
            self.assertEqual(path.read_bytes(), expected)
            self.assertEqual(path.stat().st_nlink, 1, 'private reconstruction must not alias the native cache')
            path.unlink()
            self.build()
            self.assertEqual(path.read_bytes(), expected)

        self.write('Audit.lean', 'def audit : False := True.intro\n')
        self.build(success=False)
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
    def test_native_no_build_rejects_corruption_without_production(self):
        cases = [('modules/D5.Alone.zip', targets) for targets in [(':report',),
            ('D5.Alone:report',), (':report', 'D5.Alone:report'), ('D5.Alone:report', ':report')]]
        cases.append(('report.zip', (':report',)))
        for artifact, targets in cases:
            with self.subTest(artifact=artifact, targets=targets):
                self.build()
                path = self.root / '.lake/build/lean-inspector' / artifact
                expected = path.read_bytes()
                path.unlink()  # Never mutate a Lake cache hard link.
                path.write_bytes(b'corrupt optional artifact')
                self.write('activity.jsonl', '')
                rejected = self.run_lake('--no-build', 'build', *targets, success=False)
                self.assertIn('needs to be rebuilt', rejected.stdout + rejected.stderr)
                self.assertEqual((self.root / 'activity.jsonl').read_text(), '',
                                 'no-build must reject before repair extraction or aggregation')
                self.assertTrue(path.is_file(), 'no-build must not remove the rejected artifact')
                self.assertEqual(path.read_bytes(), b'corrupt optional artifact',
                                 'no-build must not start private reconstruction')
                recovered = self.build() if targets == (':report',) else self.run_lake('build', *targets)
                self.assertIn('inspector artifact rejected; rebuilding privately', recovered.stdout + recovered.stderr)
                self.assertEqual(path.read_bytes(), expected)
                self.assertEqual(path.stat().st_nlink, 1)
                records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
                self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'),
                                 0 if artifact == 'report.zip' else 1)
                aggregates = sum(row['count'] for row in records if row['kind'] == 'aggregate')
                if artifact == 'report.zip':
                    self.assertEqual(aggregates, 1)
                else:
                    self.assertLessEqual(aggregates, int(':report' in targets))
                self.build()
                self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.write('D5/Alone.lean', (self.root / 'D5/Alone.lean').read_text() + '-- native miss\n')
        rejected = self.run_lake('--no-build', 'build', ':report', success=False)
        self.assertIn('needs to be rebuilt', rejected.stdout + rejected.stderr)
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
    def test_public_module_validates_and_private_job_is_not_a_target(self):
        self.build()
        path = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        expected = path.read_bytes()
        before = self.stamps()
        path.unlink()
        path.write_bytes(b'corrupt optional artifact')
        self.write('activity.jsonl', '')
        result = self.run_lake('build', 'D5.Alone:report')
        self.assertIn('inspector artifact rejected; rebuilding privately', result.stdout + result.stderr)
        self.assertEqual(path.read_bytes(), expected)
        self.assertEqual(path.stat().st_nlink, 1)
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.Alone'})
        self.assertEqual([json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()],
                         [dict(kind='extract', count=1)])
        result = self.run_lake('build', 'D5.Alone:inspectorUnvalidatedReport', success=False)
        self.assertIn('unknown module facet', result.stdout + result.stderr)
        for targets in [(':report', 'D5.Alone:report'), ('D5.Alone:report', ':report')]:
            with self.subTest(targets=targets):
                path.unlink()
                path.write_bytes(b'corrupt optional artifact')
                self.write('activity.jsonl', '')
                self.run_lake('build', *targets)
                self.assertEqual(path.read_bytes(), expected)
                records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
                self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)

        # A bad optional row may trigger production, but a required producer
        # failure must fail both public module and package entrypoints.
        producer = self.root / 'tools/lean-inspector/native.py'
        producer.write_text(producer.read_text().replace(
            'def module(root, name, source, utility_path, executable, output):',
            'def module(root, name, source, utility_path, executable, output):\n'
            '    raise ValueError("required fixture producer failure")').replace(
            'def produce_batch(requests):',
            'def produce_batch(requests):\n    raise ValueError("required fixture producer failure")'))
        path.unlink()
        path.write_bytes(b'corrupt optional artifact')
        result = self.run_lake('build', 'D5.Alone:report', success=False)
        self.assertIn('required fixture producer failure', result.stdout + result.stderr)
        self.write('D5/Alone.lean', (self.root / 'D5/Alone.lean').read_text() + '-- require a new native artifact\n')
        result = self.build(success=False)
        self.assertIn('required fixture producer failure', result.stdout + result.stderr)
