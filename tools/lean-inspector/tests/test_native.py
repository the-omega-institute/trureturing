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
import zipfile
import zlib

HERE = Path(__file__).resolve().parents[1]
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))
import publication
import materials


class NativeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.lake = subprocess.check_output(['elan', 'which', 'lake'], cwd=ROOT, text=True).strip()

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='inspector-native.')
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write('lakefile.toml', '''name = "fixture"
defaultTargets = ["Fixture", "Audit"]
[[require]]
name = "leanInspector"
path = "tools/lean-inspector"
[[lean_lib]]
name = "Fixture"
roots = ["Fixture", "D5"]
globs = ["Fixture", "D5.+"]
[[lean_lib]]
name = "Audit"
globs = ["Audit"]
defaultFacets = ["static"]
''')
        self.write('Fixture.lean', 'import D5.A\ntheorem result : ¬ False := fun h => h\n')
        self.write('D5/A.lean', 'import D5.B\ndef value : Nat := D5.hidden\n')
        self.write('D5/B.lean', 'module\npublic section\nnamespace D5\nprivate def secret : Nat := 1\ndef hidden : Nat := secret\n')
        self.write('D5/Alone.lean', 'def alone : String := "λ😀𐀀"\nopaque concealed : Nat := 7\n')
        self.write('External.lean', 'import ClaimSupport\ndef claim : Prop := claimSupport\n')
        self.write('ClaimSupport.lean', 'def claimSupport : Prop := False\n')
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        with (self.root / 'lakefile.toml').open('a') as target:
            target.write('[[lean_lib]]\nname = "External"\n[[lean_lib]]\nname = "ClaimSupport"\n')
        for name in ['Inspector.lean', 'lakefile.lean', 'lake-manifest.json', 'native.py', 'publication.py', 'materials.py', 'inspect.sh']:
            self.copy('tools/lean-inspector/' + name)
        for name in ['tools/scripts/report/lean-report-selection.py', 'tools/scripts/report/lean-report-input.sh',
                     'tools/scripts/worktree/lean-cache-input.sh', 'lean-toolchain',
                     'tools/StrataLint.Cli/Commands/LeanUtilityInputCommand.cs']:
            self.copy(name)
        self.write('bin/dotnet', '#!/usr/bin/env python3\nfrom pathlib import Path\nwith Path("utility-calls").open("a") as out: out.write("call\\n")\nprint(Path("utility.json").read_text())\n')
        (self.root / 'bin/dotnet').chmod(0o755)
        self.utility()
        paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
        policy = dict(schema_version=1, report_semantic_version=1, report_modules=paths('Fixture.lean', 'D5/**/*.lean'),
            inspector_sources=paths('tools/lean-inspector/Inspector.lean', 'tools/lean-inspector/lakefile.lean'),
            config_inputs=paths('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'),
            producer_scopes={'lean-report': paths('lean-report-inputs.json', 'tools/scripts/report/lean-report-selection.py',
                'tools/lean-inspector/Inspector.lean', 'tools/lean-inspector/lakefile.lean',
                'tools/lean-inspector/native.py', 'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                'tools/scripts/report/lean-report-input.sh', 'tools/StrataLint.Cli/Commands/LeanUtilityInputCommand.cs'),
                'scribe-content': dict(include=[], exclude=[])})
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'],
            LAKE_CACHE_DIR=str(self.root / '.lake/artifact-cache'), LAKE_ARTIFACT_CACHE='true', LAKE_RESTORE_ARTIFACTS='true',
            STRATALINT_LEAN_INPUT_MEMO_ROOT=str(self.root / '.lake/input-memo'),
            STRATALINT_INSPECTOR_ACTIVITY=str(self.root / 'activity.jsonl'))

    def copy(self, name):
        target = self.root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)
        target.chmod(0o755 if name.endswith('.sh') else 0o644)

    def write(self, name, value):
        target = self.root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(value)

    def utility(self, claim='claim'):
        self.write('utility.json', json.dumps([dict(modulePath='Fixture.lean', claimGid='claim-gid', claimModule='External',
            claimSelector=claim, claimSourcePath='External.lean', claimSourceSha256='sha256:' + publication.digest(self.root / 'External.lean'),
            resultGid='result-gid', resultModule='Fixture', resultSelector='result')]))

    def run_lake(self, *args, success=True):
        result = subprocess.run([self.lake, *args], cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        else:
            self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        return result

    def build(self, success=True):
        self.write('activity.jsonl', '')
        return self.run_lake('build', ':report', success=success)

    def stamps(self):
        return {p.stem: (p.stat().st_mtime_ns, publication.digest(p)) for p in (self.root / '.lake/build/lean-inspector/modules').glob('*.zip')}

    def report(self):
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            report = publication.unpack(self.root / '.lake/build/lean-inspector/report.zip', directory)
            rows = publication.validate_bundle(report)
            return rows, report.read_bytes(), publication.member(report, '.materials.zip').read_bytes()

    def test_native_invalidation(self):
        self.build()
        rows, original_report, original_materials = self.report()
        self.assertEqual(len(rows), 4)
        self.assertTrue(rows[-1]['utility_refutation']['is_closed_negation'])
        self.assertTrue((self.root / '.lake/build/lib/lean/Audit.olean').is_file())
        self.assertTrue(list((self.root / '.lake/build/lib').glob('*Audit*.a')))
        self.assertTrue((self.root / '.lake/build/lib/lean/External.olean').is_file())
        self.assertTrue((self.root / '.lake/build/lib/lean/D5/B.olean.private').is_file())
        self.check_census_modes(rows)
        before = self.stamps()
        self.build()
        self.assertEqual(before, self.stamps(), 'unchanged build extracted rows')
        self.assertEqual((self.root / 'activity.jsonl').read_text(), '')
        self.assertEqual(self.report()[1:], (original_report, original_materials))

        def changed(expected):
            nonlocal before
            self.build()
            after = self.stamps()
            actual = {name for name in after if after[name] != before.get(name)}
            self.assertEqual(actual, set(expected))
            before = after
            records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
            self.assertEqual(sum(r['count'] for r in records if r['kind'] == 'extract'), len(expected))

        self.write('D5/B.lean', (self.root / 'D5/B.lean').read_text().replace(':= 1', ':= 2'))
        changed(['D5.B', 'D5.A', 'Fixture'])
        self.write('D5/Alone.lean', (self.root / 'D5/Alone.lean').read_text() + '-- raw source bytes\n')
        changed(['D5.Alone'])
        self.write('ClaimSupport.lean', 'def claimSupport : Prop := True\n')
        changed(['Fixture'])
        self.assertFalse(self.report()[0][-1]['utility_refutation']['is_closed_negation'])
        self.write('External.lean', 'def claim : Prop := True\n')
        self.utility()
        changed(['Fixture'])
        self.assertFalse(self.report()[0][-1]['utility_refutation']['is_closed_negation'])
        self.utility('absent')
        changed(['Fixture'])
        self.write('D5/Added.lean', 'def added : Nat := 3\n')
        changed(['D5.Added'])
        (self.root / 'D5/Added.lean').unlink()
        self.build()
        self.assertNotIn('D5.Added', [row['module'] for row in self.report()[0]])
        self.write('Audit.lean', 'def audit : Nat := 2\n')
        changed([])

    def origins(self):
        with zipfile.ZipFile(self.root / '.lake/build/lean-inspector/report.zip') as archive:
            return json.loads(archive.read(publication.RAW + '.provenance.json'))['module_origins']

    def publish(self):
        result = subprocess.run([sys.executable, str(self.root / 'tools/lean-inspector/native.py'),
            'publish', str(self.root), str(self.root / 'public.json')], env=self.env,
            text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        publication.validate_bundle(self.root / 'public.json', publication.coordinates(self.root), self.root)
        result = subprocess.run(['bash', str(self.root / 'tools/scripts/report/lean-report-input.sh'),
            'verify', '--repository', str(self.root), '--report', str(self.root / 'public.json')],
            env=self.env, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

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

    def test_native_semantic_version_and_config(self):
        self.build()
        before = self.stamps()
        original = self.report()[1:]
        origins = self.origins()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_semantic_version'] = 2
        self.write('lean-report-inputs.json', json.dumps(policy))
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

    def check_row_decoder_recovery(self, damage, exception):
        self.build()
        before = self.stamps()
        expected_report = self.report()
        origins = self.origins()
        path = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        expected = path.read_bytes()
        damaged = damage(expected)
        # Establish the real decoder failure before testing Lake's optional-row
        # recovery. Replace the private path, never a native-cache hard link.
        path.unlink()
        path.write_bytes(damaged)
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            with self.assertRaises(exception):
                report = publication.unpack(path, directory, ('', '.materials.zip', '.provenance.json'))
                publication.validate_rows(report, publication.member(report, '.materials.zip'))
        recovered = self.build()
        self.assertIn('inspector artifact rejected; rebuilding privately', recovered.stdout + recovered.stderr)
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.Alone'})
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)
        self.assertEqual(path.read_bytes(), expected)
        self.assertEqual(path.stat().st_nlink, 1, 'reconstruction must be private')
        self.assertEqual(self.report(), expected_report)
        self.assertEqual(self.origins(), origins)

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

    def test_native_pack_unpack_reuses_complete_rows(self):
        self.build()
        expected = self.report()[1:]
        archive = self.root / 'native.tar.gz'
        self.run_lake('pack', str(archive))
        self.assertTrue(archive.is_file())
        shutil.rmtree(self.root / '.lake/build')
        self.run_lake('unpack', str(archive))
        before = self.stamps()
        self.build()
        self.assertEqual(before, self.stamps())
        self.assertEqual(expected, self.report()[1:])
        before = self.stamps()
        self.write('D5/Alone.lean', 'def alone : Nat := 9\n')
        result = self.run_lake('build', 'D5.Alone:report')
        self.assertIn('LEAN_INSPECTOR_EXTRACT module=D5.Alone', result.stdout + result.stderr)
        self.assertEqual({n for n, value in self.stamps().items() if value != before[n]}, {'D5.Alone'})
        self.build()
        self.assertEqual(sum(json.loads(line)['count'] for line in (self.root / 'activity.jsonl').read_text().splitlines()
                             if json.loads(line)['kind'] == 'extract'), 0)
        self.publish()

    def test_snapshot_generation_preserves_lean_address(self):
        self.write('Trureturing.lean', 'import Fixture\n')
        self.write('lake-manifest.json', '{"version":"1.2.0","packages":[]}\n')
        helper = self.root / 'tools/scripts/worktree/lean-cache-input.sh'
        def address(command):
            return subprocess.check_output([str(helper), command, '--repository', str(self.root)],
                cwd=self.root, env=self.env, text=True, timeout=120)
        lean_before, snapshot_before = address('address'), address('build-snapshot-address')
        self.write('tools/lean-inspector/materials.py', '# changed producer bytes\n')
        self.assertEqual(lean_before, address('address'))
        self.assertEqual(snapshot_before, address('build-snapshot-address'))
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_semantic_version'] = 2
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.assertEqual(lean_before, address('address'))
        self.assertNotEqual(snapshot_before, address('build-snapshot-address'))
        (self.root / 'tools/lean-inspector/materials.py').unlink()
        result = subprocess.run([str(helper), 'build-snapshot-address', '--repository', str(self.root)],
            cwd=self.root, env=self.env, capture_output=True, timeout=120)
        self.assertNotEqual(result.returncode, 0)

    def check_census_modes(self, rows):
        module = next(row for row in rows if row['module'] == 'D5.B')
        hidden = next(decl for decl in module['declarations'] if decl['name'] == 'D5.hidden')
        secret = next(decl for decl in module['declarations'] if decl['name'].endswith('.secret'))
        olean = self.root / '.lake/build/lib/lean/D5/B.olean'
        parts = [str(olean) + suffix for suffix in ['', '.server', '.private']]
        self.write('dependencies.json', json.dumps([['D5.B', parts]]))
        self.write('identity.json', json.dumps({'keys': [['D5.B', hidden['name_key']]]}))
        executable = self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'
        def inspect(*args):
            output = subprocess.check_output([str(executable), *args], cwd=self.root, env=self.env, text=True, timeout=120)
            return [json.loads(line) for line in output.splitlines()]
        bodies = inspect('--dependencies', 'dependencies.json', '-', 'bodies')
        hidden_body = next(row for row in bodies if row.get('name') == hidden['name_key'] and row['value'] is not None)
        self.assertIn(secret['name_key'], hidden_body['value'])
        names = inspect('--dependencies', 'dependencies.json', '-', 'names')
        self.assertEqual({r['name'] for r in bodies if 'name' in r}, {r['name'] for r in names if 'name' in r})
        identities = inspect('--statement-identities', 'dependencies.json', 'identity.json')
        self.assertTrue(identities)
        self.assertIn(hidden['statement_id'],
            {materials.declaration_statement_id(module['source_path'], hidden['kind'], hidden['name_key'], r['statement_material'])
             for r in identities if r['part'] == 'private'})


if __name__ == '__main__':
    unittest.main()
