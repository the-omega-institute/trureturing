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



class NativeTestSupport:
    @classmethod
    def setUpClass(cls):
        cls.lake = os.environ.get('STRATALINT_NATIVE_LAKE_BIN') or subprocess.check_output(
            ['elan', 'which', 'lake'], cwd=ROOT, text=True).strip()
        cls.dotnet = shutil.which('dotnet')
        cls.cli = Path(os.environ.get('STRATALINT_NATIVE_DOTNET_CLI',
            ROOT / 'tools/StrataLint.Lean/bin/Release/net10.0/StrataLint.Lean.dll'))
        if not cls.dotnet or not cls.cli.is_file():
            raise RuntimeError('native fixtures require make -C tools dotnet first')
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix='inspector-native.',
            dir=os.environ.get('STRATALINT_NATIVE_TMPDIR'))
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.write('lakefile.toml', '''name = "fixture"
defaultTargets = ["Fixture", "Audit"]
[[require]]
name = "leanInspector"
path = "tools/lean-inspector"
[[require]]
name = "mathlib"
path = "fixture-mathlib"
[[lean_lib]]
name = "Fixture"
roots = ["Fixture", "D5"]
globs = ["Fixture", "D5.+"]
[[lean_lib]]
name = "Audit"
globs = ["Audit"]
defaultFacets = ["static"]
[[lean_exe]]
name = "cache"
root = "Cache"
''')
        # No external dependencies need downloading. Let the actual ensure
        # owner invoke this fixture cache provider before the first raw Lake
        # build; only that owner creates the stamp and admits donor seeding.
        self.write('fixture-mathlib/lakefile.toml', 'name = "mathlib"\n')
        self.write('fixture-mathlib/lake-manifest.json', '{"version":"1.2.0","packages":[]}\n')
        self.write('Cache.lean', 'def main : IO Unit := pure ()\n')
        self.write('lake-manifest.json', json.dumps(dict(version='1.2.0',
            packagesDir='.lake/packages', packages=[dict(type='path', scope='',
                name='leanInspector', manifestFile='lake-manifest.json', inherited=False,
                dir='tools/lean-inspector', configFile='lakefile.lean'),
                dict(type='path', scope='', name='mathlib', manifestFile='lake-manifest.json', inherited=False,
                    dir='fixture-mathlib', configFile='lakefile.toml', rev='0123456789abcdef0123456789abcdef01234567')],
            name='fixture', lakeDir='.lake', fixedToolchain=False)))
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
                     'tools/scripts/worktree/lean-cache-input.sh', 'tools/scripts/worktree/lean_cache.py',
                     'tools/scripts/worktree/cache_material.py', 'tools/scripts/worktree/cache_deadline.py',
                     'lean-toolchain', 'Makefile',
                     'tools/scripts/worktree/lean-cache-ensure.sh', 'tools/scripts/worktree/lean-cache-run.sh',
                     'tools/scripts/report/lean-report.sh', 'tools/scripts/report/report-supervisor.sh',
                     'tools/scripts/lib/resource-observation-lib.sh',
                     'tools/StrataLint.Lean/Lean/LeanUtilityInputCommand.cs']:
            self.copy(name)
        self.write('bin/dotnet', '#!/usr/bin/env python3\nimport os, sys\nfrom pathlib import Path\n'
            + f'dotnet, cli = {self.dotnet!r}, {str(self.cli)!r}\n'
            + 'operation = next((word for word in sys.argv if word in ("ensure-cache", "with-cache-writer", "with-cache-reader")), None)\n'
            + 'if operation: os.execv(dotnet, [dotnet, cli, *sys.argv[sys.argv.index(operation):]])\n'
            + 'if sys.argv[1] == "build": raise SystemExit(0)  # utility input is fixture data\n'
            + 'if sys.argv[-1] != "lean-utility-input": raise SystemExit("unexpected fixture dotnet command")\n'
            + 'with Path("utility-calls").open("a") as out: out.write("call\\n")\n'
            + 'print(Path("utility.json").read_text())\n')
        (self.root / 'bin/dotnet').chmod(0o755)
        self.utility()
        paths = lambda *names: dict(include=[dict(pattern=n, optional=False) for n in names], exclude=[])
        policy = dict(schema_version=1, report_semantic_version=1, report_modules=paths('Fixture.lean', 'D5/**/*.lean'),
            inspector_sources=paths('tools/lean-inspector/Inspector.lean', 'tools/lean-inspector/lakefile.lean'),
            dependency_sources=paths('External.lean', 'ClaimSupport.lean'),
            config_inputs=paths('lean-toolchain', 'lakefile.toml', 'lake-manifest.json'),
            producer_scopes={'lean-report': paths('lean-report-inputs.json', 'tools/scripts/report/lean-report-selection.py',
                'tools/lean-inspector/Inspector.lean', 'tools/lean-inspector/lakefile.lean',
                'tools/lean-inspector/native.py', 'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                'tools/scripts/report/lean-report-input.sh', 'tools/StrataLint.Lean/Lean/LeanUtilityInputCommand.cs'),
                'scribe-content': dict(include=[], exclude=[])})
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.env = dict(os.environ, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'], LAKE_BIN=self.lake,
            LAKE_CACHE_DIR=str(self.root / '.lake/artifact-cache'), LAKE_ARTIFACT_CACHE='true', LAKE_RESTORE_ARTIFACTS='true',
            STRATALINT_LEAN_INPUT_MEMO_ROOT=str(self.root / '.lake/input-memo'),
            STRATALINT_INSPECTOR_ACTIVITY=str(self.root / 'activity.jsonl'))
        # A fresh synthetic Git repository bounds donor discovery to this
        # fixture. No host checkout or shared donor participates.
        subprocess.run(['git', 'init', '--quiet', str(self.root)], check=True, capture_output=True)
    def ensure(self):
        result = subprocess.run(['make', 'lean-cache-ensure'], cwd=self.root, env=self.env,
            text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        return json.loads(next(line.removeprefix('LEAN_CACHE ') for line in result.stdout.splitlines()
                               if line.startswith('LEAN_CACHE ')))
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
        self.ensure()
        result = subprocess.run([self.lake, *args], cwd=self.root, env=self.env, text=True, capture_output=True, timeout=120)
        if success:
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        elif success is False:
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
    def origins(self):
        with zipfile.ZipFile(self.root / '.lake/build/lean-inspector/report.zip') as archive:
            return json.loads(archive.read(publication.RAW + '.provenance.json'))['module_origins']
    def record_result(self, phase, result, paths=()):
        """Optional external, reviewable fixture data; never a test oracle."""
        if output := os.environ.get('STRATALINT_NATIVE_RESULT_DIR'):
            output = Path(output) / self._testMethodName / phase
            output.mkdir(parents=True, exist_ok=True)
            for path in paths:
                destination = output / path.relative_to(self.root)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(path, destination)
            (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
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
    def check_row_decoder_recovery(self, damage, exception, *, no_build=False):
        self.build()
        before = self.stamps()
        expected_report = self.report()
        origins = self.origins()
        path = self.root / '.lake/build/lean-inspector/modules/D5.Alone.zip'
        expected = path.read_bytes()
        self.record_result('valid', dict(artifact_sha256=publication.digest(path),
            rows=expected_report[0], origins=origins), [path])
        damaged = damage(expected)
        # Establish the real decoder failure before testing Lake's optional-row
        # recovery. Replace the private path, never a native-cache hard link.
        path.unlink()
        path.write_bytes(damaged)
        with tempfile.TemporaryDirectory(dir=self.root) as directory:
            with self.assertRaises(exception):
                report = publication.unpack(path, directory, ('', '.materials.zip', '.provenance.json'))
                publication.validate_rows(report, publication.member(report, '.materials.zip'))
        self.record_result('damaged', dict(artifact_sha256=publication.digest(path),
            exception=exception.__name__), [path])
        if no_build:
            self.write('activity.jsonl', '')
            stamp = (path.stat().st_ino, path.stat().st_mtime_ns)
            rejected = self.run_lake('--no-build', 'build', ':report', success=False)
            result = dict(exit_code=rejected.returncode,
                needs_rebuild='needs to be rebuilt' in rejected.stdout + rejected.stderr,
                no_activity=(self.root / 'activity.jsonl').read_text() == '',
                artifact_unchanged=path.read_bytes() == damaged and
                    stamp == (path.stat().st_ino, path.stat().st_mtime_ns))
            self.record_result('no-build', result)
            self.assertTrue(result['no_activity'])
            self.assertTrue(result['artifact_unchanged'])
        recovered = self.build(success=None)
        self.record_result('recovery', dict(exit_code=recovered.returncode,
            private_rebuilds=(recovered.stdout + recovered.stderr).count(
                'inspector artifact rejected; rebuilding privately'),
            decoder_escaped='LZMAError:' in recovered.stdout + recovered.stderr))
        self.assertEqual(recovered.returncode, 0, recovered.stdout + recovered.stderr)
        if no_build:
            self.assertTrue(result['needs_rebuild'], rejected.stdout + rejected.stderr)
        self.assertIn('inspector artifact rejected; rebuilding privately', recovered.stdout + recovered.stderr)
        self.assertEqual({name for name, stamp in self.stamps().items() if stamp != before[name]}, {'D5.Alone'})
        records = [json.loads(line) for line in (self.root / 'activity.jsonl').read_text().splitlines()]
        self.assertEqual(sum(row['count'] for row in records if row['kind'] == 'extract'), 1)
        self.assertEqual(path.read_bytes(), expected)
        self.assertEqual(path.stat().st_nlink, 1, 'reconstruction must be private')
        self.assertEqual(self.report(), expected_report)
        self.assertEqual(self.origins(), origins)
        self.record_result('recovered', dict(artifact_sha256=publication.digest(path),
            extraction_count=sum(row['count'] for row in records if row['kind'] == 'extract'),
            private_links=path.stat().st_nlink, report_matches_valid=True, origins_preserved=True), [path])
    def encrypted_member(self, data):
        with zipfile.ZipFile(io.BytesIO(data)) as archive:
            offset = archive.start_dir + 8
        damaged = bytearray(data)
        self.assertEqual(damaged[offset] & 1, 0)
        damaged[offset] ^= 1
        return bytes(damaged)
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
