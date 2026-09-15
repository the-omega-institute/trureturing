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

    def release_fixture(self):
        """Real publisher/Inspector/Lake, with only GitHub transport replaced."""
        self.copy('tools/scripts/worktree/lean-cache-publish.sh')
        self.write('Trureturing.lean', 'import Fixture\n')
        self.env.update(STRATALINT_CACHE_REPO='fixture/cache', GITHUB_SHA='a' * 40,
            GITHUB_RUN_ID='4242', RELEASE_FIXTURE=str(self.root / 'releases'),
            STRATALINT_LEAN_INPUT_MEMO_ROOT=str(self.root / 'input-memo'),
            STRATALINT_SUPERVISOR_ROOT=str(self.root / 'supervisor'))
        self.write('bin/gh', '''#!/usr/bin/env python3
import hashlib, json, os, shutil, sys
from pathlib import Path
root = Path(os.environ['RELEASE_FIXTURE'])
root.mkdir(exist_ok=True)
a = sys.argv[1:]
if a[:2] == ['release', 'view']:
    if not (root / a[2]).is_dir(): raise SystemExit(1)
    if '--json' in a:
        print(json.dumps(dict(isDraft=False, tagName=a[2])))
    raise SystemExit(0)
if a[:2] == ['release', 'list']:
    print('\\n'.join(p.name for p in sorted(root.iterdir(), key=lambda p: p.stat().st_mtime_ns, reverse=True)))
elif a[:2] == ['release', 'create']:
    destination = root / a[2]
    destination.mkdir()
    assert a[a.index('--repo') + 1] == 'fixture/cache'
    assert a[a.index('--target') + 1] == os.environ['GITHUB_SHA']
    for item in a[3:]:
        if item.startswith('/') and Path(item).is_file(): shutil.copyfile(item, destination / Path(item).name)
elif a[:2] == ['release', 'download']:
    assert a[a.index('--repo') + 1] == 'fixture/cache'
    matches = list((root / a[2]).glob(a[a.index('--pattern') + 1]))
    if not matches: raise SystemExit(1)
    for item in matches: shutil.copyfile(item, Path(a[a.index('--dir') + 1]) / item.name)
elif a[0] == 'api' and a[1].startswith('repos/fixture/cache/releases/tags/'):
    destination = root / a[1].split('/')[-1]
    print(json.dumps(dict(target_commitish=os.environ['GITHUB_SHA'], assets=[
        dict(name=p.name, digest='sha256:' + hashlib.sha256(p.read_bytes()).hexdigest())
        for p in destination.iterdir()])))
else:
    raise SystemExit('unexpected transport call: ' + repr(a))
''')
        (self.root / 'bin/gh').chmod(0o755)

    def release_run(self, verb, success=True):
        # Run outside the repository; explicit repository paths must be sufficient.
        result = self.guarded_command(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
            verb, '--repository', str(self.root)], cwd=self.root.parent, env=self.env,
            text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def release_address(self):
        return dict(line.split('=', 1) for line in self.release_run('address').stdout.splitlines())

    def test_release_publisher_legacy_seed_current_pack_restore_and_unchanged(self):
        self.release_fixture()
        self.run_lake('build')
        address = self.release_address()
        legacy = address['tag'].rsplit('-', 1)[0]
        directory = self.root / 'releases' / legacy
        directory.mkdir(parents=True)
        archive = directory / 'lean-build.tgz'
        self.run_lake('pack', str(archive))
        self.write(str(directory.relative_to(self.root) / 'manifest.txt'), ''.join(
            f'{k}={v}\n' for k, v in dict(toolchain=address['toolchain'],
                config_sha256=address['config_sha256'], sources_sha256=address['sources_sha256'],
                archive_sha256=publication.digest(archive), producer_commit_sha=self.env['GITHUB_SHA'],
                workflow_run_id='4242').items()))
        shutil.rmtree(self.root / '.lake/build')
        restored = self.release_run('fetch')
        self.assertIn('"mode":"prefix"', restored.stdout)
        self.assertIn('"resolved":"' + legacy + '"', restored.stdout)
        self.assertFalse((self.root / '.lake/build/lean-inspector/report.zip').exists())
        # The documented manual path must prepare a report despite the legacy tag.
        first = self.guarded_command(['make', 'lean-cache-to-github-without-mathlib'], cwd=self.root,
            env=self.env, text=True, capture_output=True, timeout=120)
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        self.assertIn('"status":"published"', first.stdout)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=4 aggregates=1', first.stdout)
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        expected = {suffix: publication.member(output, suffix).read_bytes() for suffix in publication.SUFFIXES}
        publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        stamps, origins = self.stamps(), self.origins()
        new_release = self.root / 'releases' / address['tag']
        self.assertIn('build_snapshot_sha256=' + address['build_snapshot_sha256'],
            (new_release / 'manifest.txt').read_text())
        # Fetch the actual packed archive and validate the restored canonical outputs.
        shutil.rmtree(self.root / '.lake/build')
        restored = self.release_run('fetch')
        self.assertIn('"mode":"exact"', restored.stdout)
        self.assertEqual(expected, {suffix: publication.member(output, suffix).read_bytes()
            for suffix in publication.SUFFIXES})
        publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        self.assertTrue((self.root / '.lake/build/lean-inspector/report.zip').is_file())
        self.assertTrue((self.root / '.lake/build/lean-inspector/producer/bin/reportInspector').is_file())
        restored_stamps = self.stamps()  # archive transport need not preserve nanoseconds
        unchanged = self.release_run('publish')
        self.assertIn('"status":"exists"', unchanged.stdout)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', unchanged.stdout)
        self.assertEqual(restored_stamps, self.stamps())
        self.assertEqual({k: v[1] for k, v in stamps.items()}, {k: v[1] for k, v in self.stamps().items()})
        self.assertEqual(origins, self.origins())
        for suffix in publication.SUFFIXES:
            actual = publication.member(output, suffix).read_bytes()
            if suffix == '.provenance.json':
                provenance = json.loads(expected[suffix])
                provenance['mode'] = 'cached'  # Invocation mode, not a generation origin.
                self.assertEqual(provenance, json.loads(actual))
            else:
                self.assertEqual(expected[suffix], actual)
        # Same tag, but a default compiler obligation now fails: no exists success.
        self.write('Audit.lean', 'this is not valid Lean\n')
        failed = self.release_run('publish', success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=report', failed.stderr)
        self.assertNotIn('LEAN_CACHE_PUBLISH ', failed.stdout)
        self.assertEqual({legacy, address['tag']}, {p.name for p in (self.root / 'releases').iterdir()})
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        # Inject a validator failure without changing its production caller. A
        # report error must also prevent the existing-tag success and any upload.
        validator = self.root / 'tools/lean-inspector/publication.py'
        validator.write_text(validator.read_text() + '\ndef validate_bundle(*args, **kwargs):\n'
            + '    raise ValueError("fixture required report validation failed")\n')
        rejected = self.release_run('publish', success=False)
        self.assertIn('fixture required report validation failed', rejected.stdout + rejected.stderr)
        self.assertNotIn('LEAN_CACHE_PUBLISH ', rejected.stdout)
        self.assertEqual({legacy, address['tag']}, {p.name for p in (self.root / 'releases').iterdir()})
        self.record_result('publication', dict(legacy_mode='prefix', restore_mode='exact',
            restored_bundle_parity=True, unchanged_extracted_modules=0, unchanged_aggregates=0,
            required_default_failure_exit=failed.returncode, required_validation_failure_exit=rejected.returncode,
            tag=address['tag']))

    def test_release_identity_tracks_report_semantics_and_selection(self):
        self.release_fixture()
        before = self.release_address()
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_semantic_version'] += 1
        self.write('lean-report-inputs.json', json.dumps(policy))
        semantic = self.release_address()
        policy['report_modules']['exclude'] = ['D5/Alone.lean']
        self.write('lean-report-inputs.json', json.dumps(policy))
        selection = self.release_address()
        for after in [semantic, selection]:
            self.assertEqual(before['sources_sha256'], after['sources_sha256'])
            self.assertEqual(before['config_sha256'], after['config_sha256'])
        self.assertEqual(len({a['tag'] for a in [before, semantic, selection]}), 3)
        helper = self.root / 'tools/scripts/worktree/lean-cache-input.sh'
        snapshot = subprocess.check_output([str(helper), 'build-snapshot-address', '--repository', str(self.root)],
            cwd=self.root.parent, env=self.env, text=True).strip()
        self.assertEqual(selection['build_snapshot_sha256'], snapshot)
        self.assertFalse((self.root / '.lake').exists(), 'addressing must preserve cold donor eligibility')
        (self.root / 'tools/lean-inspector/materials.py').unlink()
        failed = self.release_run('publish', success=False)
        self.assertIn('snapshot address is unavailable', failed.stderr)
        self.assertFalse((self.root / 'releases').exists())
