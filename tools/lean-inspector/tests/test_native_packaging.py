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

class NativePackagingTests:
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
    def test_native_clonefile_seed_reuses_rows_and_keeps_donor_private(self):
        self.build()
        donor = self.root
        expected = self.report()[1:]
        origins = self.origins()
        donor_bytes = {p.relative_to(donor): publication.digest(p)
                       for p in (donor / '.lake').rglob('*') if p.is_file()}
        self.write('.gitignore', '.lake/\nactivity.jsonl\nutility-calls\n')

        def git(*args):
            result = subprocess.run(['git', *args], cwd=donor, env=self.env,
                text=True, capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

        git('add', '.')
        git('-c', 'user.name=Fixture', '-c', 'user.email=fixture@example.invalid',
            '-c', 'commit.gpgsign=false', 'commit', '--quiet', '-m', 'private native fixture')
        with tempfile.TemporaryDirectory(prefix='inspector-clone.') as directory:
            clone = Path(directory) / 'worktree'
            git('worktree', 'add', '--detach', str(clone), 'HEAD')
            self.root = clone
            self.env = dict(self.env, PATH=str(clone / 'bin') + os.pathsep + os.environ['PATH'],
                LAKE_CACHE_DIR=str(clone / '.lake/artifact-cache'),
                STRATALINT_LEAN_INPUT_MEMO_ROOT=str(clone / '.lake/input-memo'),
                STRATALINT_INSPECTOR_ACTIVITY=str(clone / 'activity.jsonl'),
                STRATALINT_SUPERVISOR_ROOT=str(Path(directory) / 'supervisor'))
            self.assertFalse((clone / '.lake').exists(), 'ensure must retain donor eligibility')
            manifest = (clone / 'lean-report-inputs.json').read_text()
            self.write('lean-report-inputs.json', manifest.replace('"report_semantic_version": 1',
                                                                 '"report_semantic_version": 0'))
            rejected = subprocess.run(['make', 'lean-report'], cwd=clone, env=self.env,
                text=True, capture_output=True, timeout=120)
            self.assertNotEqual(rejected.returncode, 0, rejected.stdout + rejected.stderr)
            self.assertIn('report_semantic_version', rejected.stderr)
            self.assertFalse((clone / '.lake').exists(), 'rejected inputs must preserve donor eligibility')
            self.write('lean-report-inputs.json', manifest)
            result = subprocess.run(['make', 'lean-report'], cwd=clone, env=self.env,
                text=True, capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            output = clone / '.lake/build/stratalint/raw-lean-report.json'
            logs = Path(str(output) + '.logs')
            receipt = json.loads(next(line.removeprefix('LEAN_CACHE ')
                for line in (logs / 'ensure.stdout.log').read_text().splitlines() if line.startswith('LEAN_CACHE ')))
            self.assertEqual(receipt['status'], 'seeded')
            self.assertEqual(receipt['method'], 'clonefile' if sys.platform == 'darwin' else 'copy')
            self.assertEqual(Path(receipt['donor']).resolve(), donor.resolve())
            self.assertEqual(receipt['project_olean_state'], 'warm')
            self.assertFalse((clone / '.lake').is_symlink())
            self.assertEqual((logs / 'native-work.jsonl').read_text(), '')
            publication.validate_bundle(output, publication.coordinates(clone), clone)
            self.assertEqual(output.read_bytes(), expected[0])
            self.assertEqual(publication.member(output, '.materials.zip').read_bytes(), expected[1])
            for phase in ['inputs', 'utility-input-build', 'ensure', 'report', 'publish']:
                self.assertEqual((logs / (phase + '.exit.log')).read_text(), '0\n')
            row = Path('.lake/build/lean-inspector/modules/D5.Alone.zip')
            self.assertNotEqual((donor / row).stat().st_ino, (clone / row).stat().st_ino)
            before = self.stamps()
            self.write('activity.jsonl', '')
            # Exercise the restored production writer with the native package
            # facet against real cloned build outputs.
            result = subprocess.run(['make', 'lean', 'LEAN_TARGETS=:report'], cwd=clone,
                env=self.env, text=True, capture_output=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertEqual(before, self.stamps())
            self.assertEqual((clone / 'activity.jsonl').read_text(), '')
            self.assertEqual(expected, self.report()[1:])
            self.assertEqual(origins, self.origins())
            self.write('D5/Alone.lean', 'def alone : Nat := 9\n')
            self.build()
            self.assertEqual({n for n, value in self.stamps().items() if value != before[n]}, {'D5.Alone'})
            self.publish()
            self.assertEqual(donor_bytes, {p.relative_to(donor): publication.digest(p)
                for p in (donor / '.lake').rglob('*') if p.is_file()})
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
