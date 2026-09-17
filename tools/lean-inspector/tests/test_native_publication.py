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

class NativePublicationTests:
    def test_aggregation_validates_each_row_once_and_preserves_rejection_statuses(self):
        self.build()
        state = native.state(self.root)
        config = publication.read_json((state / 'inputs.json').read_bytes())
        artifacts = [str(state / 'modules' / (name + '.zip')) for name in config['modules']]
        requests = [['validate', [str(self.root), 'module', str(self.root), name,
            str(state / 'inputs' / (name + '.json')), artifact]]
            for name, artifact in zip(config['modules'], artifacts)]
        output, request, result = (self.root / name for name in ['aggregate.zip', 'requests.json', 'statuses.json'])
        requests.append(['aggregate', [str(self.root), str(output), *artifacts]])
        # Lake's FilePath.join preserves the root package's /./ component.
        # These must take the same complete shared validation boundary.
        requests = [[kind, [arg.replace(str(self.root) + '/', str(self.root) + '/./')
            if arg.startswith(str(self.root) + '/') else
            str(self.root) + '/.' if arg == str(self.root) else arg for arg in args]]
            for kind, args in requests]
        request.write_text(json.dumps(requests))
        with patch.object(publication, 'validate_rows', wraps=publication.validate_rows) as validations:
            native.batch(request, result)
            self.assertEqual(json.loads(result.read_text()), [0] * len(requests))
            self.assertEqual(validations.call_count, len(artifacts), '[FAIL] aggregate_row_validated_once')
        self.assertEqual(output.read_bytes(), (state / 'report.zip').read_bytes())
        original = output.read_bytes()
        alone_index = config['modules'].index('D5.Alone')
        artifact = Path(artifacts[alone_index])
        good_artifact = artifact.read_bytes()
        source = self.root / 'D5/Alone.lean'
        good_source = source.read_bytes()
        for damage in ['artifact', 'source']:
            with self.subTest(damage=damage):
                if damage == 'artifact':
                    artifact.unlink()  # Never write through Lake's cache hard link.
                    artifact.write_bytes(b'not a ZIP')
                else:
                    source.write_bytes(good_source + b'\n-- changed after prior validation\n')
                try:
                    native.batch(request, result)
                    expected = [0] * len(requests)
                    expected[alone_index] = expected[-1] = 1
                    self.assertEqual(json.loads(result.read_text()), expected,
                                     '[FAIL] aggregate_exact_row_rejection')
                    self.assertEqual(output.read_bytes(), original)
                finally:
                    artifact.unlink()
                    artifact.write_bytes(good_artifact)
                    source.write_bytes(good_source)
        driver = self.root / 'LeanInformationAudit/Registry.lean'
        good_driver = driver.read_bytes()
        driver.write_bytes(good_driver + b'\n-- changed shared driver\n')
        try:
            native.batch(request, result)
            self.assertEqual(json.loads(result.read_text()), [1] * len(requests),
                             '[FAIL] aggregate_shared_source_rejection')
            self.assertEqual(output.read_bytes(), original)
        finally:
            driver.write_bytes(good_driver)
        native.batch(request, result)
        self.assertEqual(json.loads(result.read_text()), [0] * len(requests))

    def test_coordinates_use_private_temporary_memo_and_clean_up_failures(self):
        temporary = self.root / 'coordinate temporary files'
        temporary.mkdir()
        environment = dict(self.env, TMPDIR=str(temporary))
        check_output = subprocess.check_output
        observed = []
        for fault in ['none', 'none', 'address-error', 'address-malformed',
                      'coordinates-error', 'coordinates-malformed']:
            with self.subTest(fault=fault):
                def invoke(argv, **kwargs):
                    if argv[1] == 'address':
                        memo = Path(kwargs['env']['STRATALINT_LEAN_INPUT_MEMO_ROOT'])
                        self.assertEqual(memo.parent, temporary)
                        self.assertTrue(memo.is_dir())
                        self.assertEqual(memo.stat().st_mode & 0o777, 0o700)
                        observed.append(memo)
                    result = check_output(argv, **kwargs)
                    if fault == argv[1] + '-error':
                        raise subprocess.CalledProcessError(2, argv)
                    if fault == argv[1] + '-malformed':
                        return 'malformed\n'
                    return result
                with patch.dict(os.environ, environment), patch.object(
                        publication.subprocess, 'check_output', side_effect=invoke):
                    if fault == 'none':
                        result = publication.coordinates(self.root)
                        self.assertEqual(set(result), {'repository', 'producer', 'sources', 'config', 'input'})
                    else:
                        error = subprocess.CalledProcessError if fault.endswith('-error') else ValueError
                        with self.assertRaises(error):
                            publication.coordinates(self.root)
                self.assertFalse((self.root / '.lake').exists())
                self.assertEqual(list(temporary.iterdir()), [])
        self.assertEqual(len(set(observed)), len(observed), 'each invocation must own its memo')
        with patch.dict(os.environ, dict(environment, TMPDIR=str(temporary / 'absent'))):
            with self.assertRaises(FileNotFoundError):
                publication.coordinates(self.root)
        self.assertFalse((self.root / '.lake').exists())
        self.assertEqual(list(temporary.iterdir()), [])

    def test_coordinates_reuse_warm_tree_memo(self):
        self.ensure()
        self.write('.gitignore', '.lake/\nutility-calls\nactivity.jsonl\nhash-paths\n')
        helper = self.root / 'tools/scripts/worktree/lean-cache-input.sh'
        helper.write_text(helper.read_text().replace('  hash_files_batch "$live_paths"',
            '  cat "$live_paths" >> "$FIXTURE_HASH_PATHS"\n  hash_files_batch "$live_paths"'))
        for args in [('add', '.'), ('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
                '-c', 'commit.gpgsign=false', 'commit', '--quiet', '-m', 'private memo fixture')]:
            subprocess.run(['git', *args], cwd=self.root, env=self.env,
                check=True, capture_output=True, timeout=120)
        hashes = self.root / 'hash-paths'
        environment = dict(self.env, FIXTURE_HASH_PATHS=str(hashes))
        with patch.dict(os.environ, environment):
            expected = publication.coordinates(self.root)
            self.assertTrue(hashes.read_bytes())
            memo = self.root / '.lake/lean-input-memo/memo.v1'
            before = (memo.read_bytes(), memo.stat().st_ino, memo.stat().st_mtime_ns)
            self.assertTrue(before[0])
            hashes.write_bytes(b'')
            with patch.object(publication.tempfile, 'TemporaryDirectory',
                    side_effect=AssertionError('warm tree must reuse its memo')):
                self.assertEqual(publication.coordinates(self.root), expected)
            self.assertEqual(hashes.read_bytes(), b'', 'unchanged inputs must use memoized hashes')
            self.assertEqual(before, (memo.read_bytes(), memo.stat().st_ino, memo.stat().st_mtime_ns))

    def test_input_verification_is_read_only(self):
        self.build()
        self.publish()
        helper_root = self.root / 'tools'
        report = self.root / 'public.json'
        provenance = publication.member(report, '.provenance.json')
        original = provenance.read_bytes()
        environment = dict(self.env)
        # The caller must not need a host bytecode mask or redirected cache.
        environment.pop('PYTHONDONTWRITEBYTECODE', None)
        environment.pop('PYTHONPYCACHEPREFIX', None)
        working_directory = self.root / 'foreign working directory'
        working_directory.mkdir()
        for damage in ['none', 'malformed-origin', 'missing-origin', 'stale-dependency']:
            with self.subTest(damage=damage):
                provenance.write_bytes(original)
                if damage == 'malformed-origin':
                    provenance.write_bytes(b'{invalid')
                elif damage == 'missing-origin':
                    provenance.unlink()
                elif damage == 'stale-dependency':
                    self.write('ClaimSupport.lean', 'def claimSupport : Prop := True\n')
                # Start with fresh writable source directories, as in the
                # authoritative CoverBatch snapshot. Existing pyc files would
                # conceal import-time writes on both success and error paths.
                for directory in helper_root.rglob('__pycache__'):
                    shutil.rmtree(directory)
                def snapshot():
                    paths = [helper_root, *helper_root.rglob('*'),
                             *(publication.member(report, suffix) for suffix in publication.SUFFIXES)]
                    return {str(path.relative_to(self.root)):
                            (publication.digest(path) if path.is_file() else None)
                            for path in paths if path.exists()}
                before = snapshot()
                result = subprocess.run(['bash', str(helper_root / 'scripts/report/lean-report-input.sh'),
                    'verify', '--repository', str(self.root), '--report', str(report)],
                    cwd=working_directory, env=environment, text=True, capture_output=True, timeout=120)
                if damage == 'none':
                    self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                else:
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    if damage == 'stale-dependency':
                        self.assertIn('stale dependency', result.stderr)
                self.assertEqual(before, snapshot(), result.stdout + result.stderr)
    def test_publication_validates_material_identities_once(self):
        self.build()
        rows, raw, material_bytes = self.report()
        declarations = sum(len(row['declarations']) for row in rows)
        self.assertEqual(declarations, 6)
        destination = self.root / 'public.json'
        with patch.dict(os.environ, self.env), patch.object(materials, 'material_identities',
                wraps=materials.material_identities) as identities:
            native.publish(self.root, destination)
            self.assertEqual(identities.call_count, declarations)
        self.assertEqual(destination.read_bytes(), raw)
        self.assertEqual(publication.member(destination, '.materials.zip').read_bytes(), material_bytes)
        staged = self.root / 'stage' / publication.RAW
        with patch.object(materials, 'material_identities', wraps=materials.material_identities) as identities:
            publication.publish(destination, staged, publication.coordinates(self.root), self.root)
            self.assertEqual(identities.call_count, declarations)
        publication.validate_bundle(staged, publication.coordinates(self.root), self.root)
        self.assertEqual(staged.read_bytes(), raw)
        self.assertEqual(publication.member(staged, '.materials.zip').read_bytes(), material_bytes)
        result = subprocess.run([sys.executable, str(HERE / 'publication.py'), 'stage',
            '--bundle', str(destination), '--staging-directory', str(self.root / 'cli-stage'),
            '--repository', str(self.root)], env=self.env, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.root / 'cli-stage' / publication.RAW).read_bytes(), raw)
    def test_native_publication_rejects_incoming_damage_before_normalization(self):
        self.build()
        self.publish()
        destination = self.root / 'public.json'
        before = {suffix: publication.member(destination, suffix).read_bytes() for suffix in publication.SUFFIXES}
        artifact = self.root / '.lake/build/lean-inspector/report.zip'
        with zipfile.ZipFile(artifact) as archive:
            original = [(info, archive.read(info)) for info in archive.infolist()]
        for damage in ['sha256', 'mode', 'provenance', 'identity', 'source']:
            with self.subTest(damage=damage):
                entries = []
                for info, data in original:
                    if damage == 'sha256' and info.filename.endswith('.sha256'):
                        data = b'0' * 64 + b'  raw-lean-report.json\n'
                    elif damage in ['mode', 'provenance'] and info.filename.endswith('.provenance.json'):
                        value = json.loads(data)
                        if damage == 'mode': value['mode'] = 'illegal'
                        else: value.pop('module_origins')
                        data = json.dumps(value).encode()
                    elif damage == 'identity' and info.filename.endswith('.materials.zip'):
                        output = io.BytesIO()
                        with zipfile.ZipFile(io.BytesIO(data)) as materials_zip, zipfile.ZipFile(output, 'w') as changed:
                            for index, entry in enumerate(materials_zip.infolist()):
                                changed.writestr(entry, b'corrupt material' if index == 0 else materials_zip.read(entry))
                        data = output.getvalue()
                    entries.append((info, data))
                if damage == 'source':
                    # Keep every sidecar and origin consistent with the forged
                    # report, so only the current source check can reject it.
                    payloads = {info.filename: data for info, data in entries}
                    value = json.loads(payloads[publication.RAW])
                    row = value['modules'][0]
                    row['source_sha256'] = 'sha256:' + '0' * 64
                    raw = materials.canonical_json(value)
                    sha = hashlib.sha256(raw).hexdigest()
                    provenance = json.loads(payloads[publication.RAW + '.provenance.json'])
                    provenance['report_sha256'] = sha
                    provenance['module_origins'][row['module']]['report_sha256'] = hashlib.sha256(
                        materials.canonical_json(dict(schema=materials.REPORT_SCHEMA, modules=[row]))).hexdigest()
                    provenance['module_origins'][row['module']]['input_sources'][row['source_path']] = '0' * 64
                    payloads[publication.RAW] = raw
                    payloads[publication.RAW + '.provenance.json'] = json.dumps(provenance).encode()
                    payloads[publication.RAW + '.sha256'] = f'{sha}  {publication.RAW}\n'.encode()
                    attestation = payloads[publication.RAW + '.input.attestation'].decode().splitlines()
                    attestation[-1] = 'report_sha256=' + sha
                    payloads[publication.RAW + '.input.attestation'] = ('\n'.join(attestation) + '\n').encode()
                    entries = [(info, payloads[info.filename]) for info, _ in entries]
                artifact.unlink()
                with zipfile.ZipFile(artifact, 'w') as archive:
                    for info, data in entries: archive.writestr(info, data)
                if damage == 'source':
                    with tempfile.TemporaryDirectory(dir=self.root) as directory:
                        report = publication.unpack(artifact, directory)
                        expected = publication.coordinates(self.root)
                        publication.validate_bundle(report, expected, manifest=self.root / 'lean-report-inputs.json')
                        with self.assertRaisesRegex(ValueError, '^report source binding mismatch$'):
                            publication.validate_bundle(report, expected, self.root)
                for activity in ['', '{"kind":"extract","count":1}\n']:
                    self.write('activity.jsonl', activity)
                    result = subprocess.run([sys.executable, str(self.root / 'tools/lean-inspector/native.py'),
                        'publish', str(self.root), str(destination)], env=self.env,
                        text=True, capture_output=True, timeout=120)
                    self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                    if damage == 'source':
                        self.assertIn('lean-inspector-native: report source binding mismatch\n', result.stderr)
                    self.assertEqual(before, {suffix: publication.member(destination, suffix).read_bytes()
                                             for suffix in publication.SUFFIXES})
    def test_publication_snapshot_integrity_and_replace_failure(self):
        self.build()
        self.publish()
        destination = self.root / 'public.json'
        before = {suffix: publication.member(destination, suffix).read_bytes() for suffix in publication.SUFFIXES}
        self.write('D5/Alone.lean', (self.root / 'D5/Alone.lean').read_text() + '-- changed publication input\n')
        self.build()
        coordinates = publication.coordinates(self.root)
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            report = publication.unpack(self.root / '.lake/build/lean-inspector/report.zip', directory)
            validate = publication.validate_bundle
            def corrupt_validated_snapshot(*args, **kwargs):
                result = validate(*args, **kwargs)
                publication.member(args[0], '.materials.zip').write_bytes(b'changed after validation')
                return result
            with patch.object(publication, 'validate_bundle', side_effect=corrupt_validated_snapshot):
                with self.assertRaisesRegex(ValueError, 'snapshot changed'):
                    publication.publish(report, destination, coordinates, self.root)
            self.assertEqual(before, {suffix: publication.member(destination, suffix).read_bytes()
                                     for suffix in publication.SUFFIXES})

            write_bytes = Path.write_bytes
            def damage_publication_update(path, data):
                if path.name.endswith('.sha256') and path.parent.name == 'bundle':
                    data += b'damaged after normalization'
                return write_bytes(path, data)
            with patch.object(Path, 'write_bytes', damage_publication_update):
                with self.assertRaisesRegex(ValueError, 'snapshot changed after validation'):
                    publication.publish(report, destination, coordinates, self.root, mode='cached')
            self.assertEqual(before, {suffix: publication.member(destination, suffix).read_bytes()
                                     for suffix in publication.SUFFIXES})

            for failed_suffix in (*publication.SUFFIXES[1:], ''):
                with self.subTest(failed_suffix=failed_suffix):
                    replace = os.replace
                    failed = False
                    def fail_one_replace(source, target):
                        nonlocal failed
                        if Path(target) == publication.member(destination, failed_suffix) and not failed:
                            failed = True
                            raise OSError('injected publication replacement failure')
                        return replace(source, target)
                    with patch.object(publication.os, 'replace', side_effect=fail_one_replace):
                        with self.assertRaisesRegex(OSError, 'replacement failure'):
                            publication.publish(report, destination, coordinates, self.root, mode='cached')
                    self.assertTrue(failed)
                    self.assertEqual(before, {suffix: publication.member(destination, suffix).read_bytes()
                                             for suffix in publication.SUFFIXES})
    def test_native_producer_inputs(self):
        self.build()
        before = self.stamps()
        origins = self.origins()
        aggregate = self.root / '.lake/build/lean-inspector/report.zip'
        aggregate_before = (aggregate.stat().st_mtime_ns, publication.digest(aggregate))
        executable = self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'
        executable_before = publication.digest(executable)
        inspector = self.root / 'tools/lean-inspector/Inspector.lean'
        # A real implementation edit changes executable bytes while preserving
        # valid report semantics. Compilation must still succeed.
        inspector.write_text(inspector.read_text().replace('expected bodies or names', 'expected census bodies or names'))
        self.build()
        self.assertNotEqual(executable_before, publication.digest(executable))
        self.assertEqual(before, self.stamps())
        self.assertEqual(origins, self.origins())
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.publish()
        published = publication.read_json(publication.member(self.root / 'public.json', '.provenance.json').read_bytes())
        self.assertEqual(published['module_origins'], origins)
        self.assertEqual(published['mode'], 'cached')
        for producer, comment in [('tools/lean-inspector/materials.py', '#'),
                                  ('tools/lean-inspector/native.py', '#'),
                                  ('tools/lean-inspector/lakefile.lean', '--'),
                                  ('tools/scripts/report/lean-report-input.sh', '#'),
                                  ('tools/StrataLint.Cli/Commands/LeanUtilityInputCommand.cs', '//')]:
            with self.subTest(producer=producer):
                calls = (self.root / 'utility-calls').read_text().splitlines()
                implementation = (self.root / producer).read_text()
                if producer.endswith('materials.py'):
                    implementation = implementation.replace('BUFFER_BYTES = 64 * 1024', 'BUFFER_BYTES = 32 * 1024')
                self.write(producer, implementation + '\n' + comment + ' compatible producer bytes\n')
                self.build()
                self.assertEqual(before, self.stamps())
                self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
                self.assertEqual(len((self.root / 'utility-calls').read_text().splitlines()), len(calls) + 1)
                self.assertEqual(origins, self.origins())
        self.write('lean-report-inputs.json', (self.root / 'lean-report-inputs.json').read_text() + '\n')
        self.build()
        self.assertEqual(before, self.stamps())
        self.assertEqual(aggregate_before, (aggregate.stat().st_mtime_ns, publication.digest(aggregate)))
        self.write('tools/lean-inspector/CompatibleHelper.lean', 'def compatibleHelper : Nat := 1\n')
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        for scope in ['inspector_sources', 'dependency_sources']:
            policy[scope]['include'].append(dict(pattern='tools/lean-inspector/CompatibleHelper.lean', optional=False))
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.build()
        self.assertEqual(before, self.stamps())
        self.assertEqual(aggregate_before, (aggregate.stat().st_mtime_ns, publication.digest(aggregate)))
        self.assertEqual(origins, self.origins())
        # Subsequent content changes assemble mixed actual production origins.
        self.write('D5/Alone.lean', (self.root / 'D5/Alone.lean').read_text() + '-- content input\n')
        self.build()
        self.assertEqual({n for n, value in self.stamps().items() if value != before[n]}, {'D5.Alone'})
        mixed = self.origins()
        for name in origins:
            if name == 'D5.Alone':
                self.assertNotEqual(origins[name]['producer_sources_sha256'], mixed[name]['producer_sources_sha256'])
                self.assertNotEqual(origins[name]['inspector_executable_sha256'], mixed[name]['inspector_executable_sha256'])
            else:
                self.assertEqual(origins[name], mixed[name])
        self.publish()
        self.build()
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.assertEqual(mixed, self.origins())
        self.publish()
        before = self.stamps()
        damaged = self.root / '.lake/build/lean-inspector/modules/D5.B.zip'
        damaged.unlink()
        damaged.write_bytes(b'corrupt row after compatible producer changes')
        self.write('activity.jsonl', '')
        self.run_lake('build', 'D5.B:report', ':report')
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)
        self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'aggregate'), 1)
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.B'})
        recovered = self.origins()
        self.assertNotEqual(mixed['D5.B']['producer_sources_sha256'], recovered['D5.B']['producer_sources_sha256'])
        for name in mixed:
            if name != 'D5.B': self.assertEqual(mixed[name], recovered[name])
        self.publish()
    def test_native_semantic_version_and_config(self):
        self.build()
        self.write('activity.jsonl', '')
        self.run_lake('--no-build', 'build', ':report')
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        before = self.stamps()
        original = self.report()[1:]
        origins = self.origins()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_semantic_version'] = 2
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.run_lake('--no-build', 'build', ':report', success=False)
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.build()
        self.assertEqual({name for name, value in self.stamps().items() if value != before[name]}, set(before))
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(r['count'] for r in records if r['kind'] == 'extract'), len(before))
        self.assertEqual(original, self.report()[1:])
        self.assertNotEqual(origins['Fixture']['compatibility_sha256'], self.origins()['Fixture']['compatibility_sha256'])
        self.publish()
        self.build()
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        before = self.stamps()
        self.write('lakefile.toml', (self.root / 'lakefile.toml').read_text() + '\n# config bytes\n')
        self.build()
        self.assertEqual({name for name, value in self.stamps().items() if value != before[name]}, set(before))
    def test_native_invalid_semantic_versions(self):
        self.build()
        before = self.stamps()
        original = (self.root / 'lean-report-inputs.json').read_text()
        for value in ['0', '-1', 'true', 'null', '"1"', '1.0', '1e0']:
            self.write('lean-report-inputs.json', original.replace('"report_semantic_version": 1', '"report_semantic_version": ' + value))
            result = self.build(success=False)
            self.assertIn('report_semantic_version', result.stdout + result.stderr)
            self.assertEqual(before, self.stamps())
            self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        for invalid in [original.replace('"report_semantic_version": 1, ', ''),
                        original.replace('"report_semantic_version": 1', '"report_semantic_version": 1, "report_semantic_version": 1')]:
            self.write('lean-report-inputs.json', invalid)
            result = self.build(success=False)
            self.assertIn('report_semantic_version', result.stdout + result.stderr)
            self.assertEqual(before, self.stamps())
            self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
