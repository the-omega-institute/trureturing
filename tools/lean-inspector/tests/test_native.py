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
import unittest
import zipfile

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
        self.write('bin/dotnet', '#!/usr/bin/env python3\nfrom pathlib import Path\nprint(Path("utility.json").read_text())\n')
        (self.root / 'bin/dotnet').chmod(0o755)
        self.utility()
        paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
        policy = dict(schema_version=1, report_modules=paths('Fixture.lean', 'D5/**/*.lean'),
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

    def test_native_producer_inputs(self):
        self.build()
        before = self.stamps()

        def changed(expected):
            nonlocal before
            self.build()
            after = self.stamps()
            self.assertEqual({name for name in after if after[name] != before.get(name)}, set(expected))
            before = after
            records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
            self.assertEqual(sum(r['count'] for r in records if r['kind'] == 'extract'), len(expected))

        # These are copies of the actual producers, not synthetic version tokens.
        for producer, comment in [('tools/lean-inspector/Inspector.lean', '--'),
                                  ('tools/lean-inspector/materials.py', '#'),
                                  ('tools/scripts/report/lean-report-input.sh', '#'),
                                  ('tools/StrataLint.Cli/Commands/LeanUtilityInputCommand.cs', '//')]:
            with self.subTest(producer=producer):
                self.write(producer, (self.root / producer).read_text() + '\n' + comment + ' producer bytes\n')
                changed(before)
                changed([])
        self.write('lean-report-inputs.json', (self.root / 'lean-report-inputs.json').read_text() + '\n')
        changed(before)
        changed([])
        self.write('lakefile.toml', (self.root / 'lakefile.toml').read_text() + '\n# config bytes\n')
        changed(before)

    def test_native_recovery_and_required_failures(self):
        self.build()
        for artifact in ['modules/D5.Alone.zip', 'report.zip']:
            path = self.root / '.lake/build/lean-inspector' / artifact
            expected = path.read_bytes()
            # Replace, never edit a hard link into Lake's artifact cache.
            path.unlink()
            path.write_bytes(b'corrupt optional artifact')
            self.build()
            self.assertEqual(path.read_bytes(), expected)
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
