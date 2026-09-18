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
    def test_mapped_image_matches_loaded_bytes(self):
        self.write('LeanInformationAudit/RegistryTypes.lean', '''import Lean
namespace LeanInformationAudit
abbrev InformationTemplateReportDriver := Array Lean.Name → Lean.MetaM (Array Lean.Json)
''')
        self.write('LeanInformationAudit/Registry.lean', '''import LeanInformationAudit.RegistryTypes
namespace LeanInformationAudit
open Lean
private structure RegionLayout where
  filePath : System.FilePath
  size : USize
  isMemoryMapped : Bool
  baseAddr : USize
  bufferOffset : USize
  root : NonScalar
@[noinline, export lean_dtr_mapped_image_match]
unsafe def mappedImageMatch (_root : NonScalar) (_coordinates : Array USize)
    (_bytes : ByteArray) : Nat := 0
unsafe def finiteInformationTemplateReportDriver : InformationTemplateReportDriver := fun names => do
  let env ← getEnv
  let some region := env.header.regions.find? (·.filePath.toString.endsWith "D5/Alone.olean")
    | throwError "setup: missing loaded native fixture"
  let view : RegionLayout := unsafeCast region
  let bytes ← IO.FS.readBinFile region.filePath
  let coordinates := #[view.size, view.baseAddr, view.bufferOffset,
    if view.isMemoryMapped then 1 else 0]
  let test (coords : Array USize) (input : ByteArray) :=
    mappedImageMatch view.root coords input == 1
  let checks := Json.mkObj [
    ("mapped_image_matches_loaded_bytes", toJson (test coordinates bytes)),
    ("mapped_image_changed_bytes_rejected", toJson (!test coordinates (bytes.set! 0 (bytes[0]! + 1)))),
    ("mapped_image_wrong_length_rejected", toJson (!test coordinates (bytes.push 0))),
    ("mapped_image_relocated_falls_back", toJson (!test (coordinates.set! 1 (view.baseAddr + 8)) bytes)),
    ("mapped_image_unmapped_falls_back", toJson (!test (coordinates.set! 3 0) bytes)),
    ("mapped_image_bad_frame_falls_back", toJson (!test #[] bytes)),
    ("mapped_image_root_out_of_range_falls_back", toJson (!test (coordinates.set! 2 view.size) bytes)),
    ("mapped_image_scalar_root_falls_back", toJson (mappedImageMatch (unsafeCast (0 : Nat)) coordinates bytes == 0))]
  let debug := s!"mapped={view.isMemoryMapped} size={view.size} base={view.baseAddr} offset={view.bufferOffset} root={ptrAddrUnsafe view.root}"
  return names.map fun _ => Json.mkObj [("checks", checks), ("debug", toJson debug)]
''')
        self.copy('tools/lean-inspector/Inspector.lean')
        self.ensure()
        built = subprocess.run(['make', 'lean',
            'LEAN_TARGETS=leanInspector/reportInspector D5.Alone LeanInformationAudit.Registry'],
            cwd=self.root, env=self.env, capture_output=True, text=True, timeout=120)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        output = self.root / 'mapped.spool.json'
        executable = self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'
        result = self.run_lake('env', str(executable), '--output', str(output),
            '--material-spool', str(self.root / 'mapped.material-spool'),
            'D5.Alone', 'D5/Alone.lean', 'sha256:' + publication.digest(self.root / 'D5/Alone.lean'),
            success=None)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        record = json.loads(output.read_text())['modules'][0]['information_templates']
        symbols = subprocess.run(['nm', '-g', str(executable)], capture_output=True, text=True)
        native_symbols = [line for line in symbols.stdout.splitlines() if 'lean_dtr_mapped_image_match' in line]
        for name, passed in record['checks'].items():
            self.assertTrue(passed, '[FAIL] ' + name + ': ' + record['debug'] + ' symbols=' + repr(native_symbols))

    def test_native_facet_supplies_toolchain_environment(self):
        self.env.pop('LEAN_SYSROOT', None)
        result = self.run_lake('build', ':report', success=None)
        self.assertEqual(result.returncode, 0,
            '[FAIL] native_toolchain_search_path\n' + result.stdout + result.stderr)
        self.assertIn('D5.Alone', self.stamps())

    def test_binding_driver_environment_survives_interpreter_shutdown(self):
        # Exercise the dynamic driver entry, including interpreter teardown.
        # These fixture records test lifetime only, not binding admission.
        self.write('LeanInformationAudit/RegistryTypes.lean', '''import Lean
namespace LeanInformationAudit
abbrev InformationTemplateReportDriver := Array Lean.Name → Lean.MetaM (Array Lean.Json)
initialize fixtureExtension : Lean.SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  Lean.registerSimplePersistentEnvExtension {
    addEntryFn := fun entries entry => entries.push entry
    addImportedFn := fun arrays => arrays.foldl (· ++ ·) #[] }
''')
        self.write('LeanInformationAudit/Registry.lean', '''import LeanInformationAudit.RegistryTypes
namespace LeanInformationAudit
def finiteInformationTemplateReportDriver : InformationTemplateReportDriver := fun names => do
  let env ← Lean.getEnv
  let entries := fixtureExtension.getState env
  return names.map fun name => Lean.Json.mkObj [
    ("fixture_root", Lean.toJson name.toString),
    ("fixture_modules", Lean.toJson env.header.moduleNames.size),
    ("fixture_entries", Lean.toJson entries.size)]
''')
        self.copy('tools/lean-inspector/Inspector.lean')
        self.ensure()
        built = subprocess.run(['make', 'lean',
            'LEAN_TARGETS=leanInspector/reportInspector D5.Alone LeanInformationAudit.Registry'],
            cwd=self.root, env=self.env, capture_output=True, text=True, timeout=120)
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        output = self.root / 'driver.spool.json'
        executable = self.root / '.lake/build/lean-inspector/producer/bin/reportInspector'
        result = self.run_lake('env', str(executable), '--output', str(output),
            '--material-spool', str(self.root / 'driver.material-spool'),
            'D5.Alone', 'D5/Alone.lean', 'sha256:' + publication.digest(self.root / 'D5/Alone.lean'),
            success=None)
        self.assertEqual(result.returncode, 0,
            '[FAIL] binding_driver_process_lifetime\n' + result.stdout + result.stderr)
        binding = json.loads(output.read_text())['modules'][0]['information_templates']
        self.assertEqual(binding['fixture_root'], 'D5.Alone')
        self.assertGreater(binding['fixture_modules'], 0)
        # The source interpreter has its own process-global IR cache. Exercise
        # that entry as well as the relocated native executable.
        result = self.run_lake('env', 'lean', '--root=tools/lean-inspector', '--run',
            'tools/lean-inspector/Inspector.lean', '--output', str(output),
            '--material-spool', str(self.root / 'source-driver.material-spool'),
            'D5.Alone', 'D5/Alone.lean', 'sha256:' + publication.digest(self.root / 'D5/Alone.lean'),
            success=None)
        self.assertEqual(result.returncode, 0,
            '[FAIL] binding_driver_process_lifetime\n' + result.stdout + result.stderr)

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
    def test_snapshot_generation_preserves_mathlib_partition(self):
        helper = self.root / 'tools/scripts/worktree/lean-cache-input.sh'
        def partition():
            return subprocess.check_output([str(helper), 'partition', '--repository', str(self.root)],
                cwd=self.root, env=self.env, text=True, timeout=120)
        before = partition()
        self.write('tools/lean-inspector/materials.py', '# changed producer bytes\n')
        self.assertEqual(before, partition())
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_semantic_version'] = 2
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.assertEqual(before, partition())
        manifest = json.loads((self.root / 'lake-manifest.json').read_text())
        next(package for package in manifest['packages'] if package['name'] == 'mathlib')['rev'] = 'f' * 40
        self.write('lake-manifest.json', json.dumps(manifest))
        self.assertNotEqual(before, partition())

    def release_fixture(self):
        """Real publisher/Inspector/Lake, with only GitHub transport replaced."""
        for name in ('lean-cache-publish.sh', 'lean_cache_release.py'):
            self.copy('tools/scripts/worktree/' + name)
        self.env.update(STRATALINT_CACHE_REPO='fixture/cache', GITHUB_SHA='a' * 40,
            GITHUB_RUN_ID='4242', GITHUB_RUN_ATTEMPT='1', GITHUB_EVENT_NAME='schedule',
            GITHUB_REF='refs/heads/dev', STRATALINT_ACTIONS_CACHE_SEEDED='',
            RELEASE_FIXTURE=str(self.root / 'releases'), LEAN_REPORT=str(self.root / 'unexpected.json'),
            STRATALINT_LEAN_INPUT_MEMO_ROOT=str(self.root / 'input-memo'),
            STRATALINT_SUPERVISOR_ROOT=str(self.root / 'supervisor'))
        self.write('bin/gh', '''#!/usr/bin/env python3
import base64, hashlib, json, os, shutil, sys
from pathlib import Path
root = Path(os.environ['RELEASE_FIXTURE'])
root.mkdir(exist_ok=True)
a = sys.argv[1:]
def metadata(directory):
    return json.loads((directory / 'release.json').read_text())
if a[:2] == ['release', 'list']:
    print(json.dumps([dict(tagName=p.name, createdAt=str(p.stat().st_mtime_ns),
        isDraft=metadata(p)['draft']) for p in root.iterdir()]))
elif a[:2] == ['release', 'create']:
    destination = root / a[2]
    destination.mkdir()
    assert a[a.index('--repo') + 1] == 'fixture/cache'
    assert '--draft' in a
    assert '--target' not in a, 'new snapshots use the default storage anchor'
    (destination / 'release.json').write_text(json.dumps(dict(tag_name=a[2], draft=True,
        target_commitish='main', published_at='fixture')))
elif a[:2] == ['release', 'upload']:
    for item in a[3:]:
        if item.startswith('/') and Path(item).is_file(): shutil.copyfile(item, root / a[2] / Path(item).name)
elif a[:2] == ['release', 'edit']:
    record = metadata(root / a[2])
    record['draft'] = False
    (root / a[2] / 'release.json').write_text(json.dumps(record))
elif a[:2] == ['release', 'download']:
    destination = Path(a[a.index('--dir') + 1])
    for index, word in enumerate(a):
        if word == '--pattern':
            matches = list((root / a[2]).glob(a[index + 1]))
            if not matches: raise SystemExit(1)
            for item in matches: shutil.copyfile(item, destination / item.name)
elif a[0] == 'api' and '/releases/tags/' in a[1]:
    directory = root / a[1].split('/')[-1]
    if not directory.exists():
        print(json.dumps(dict(message='Not Found', status='404')))
        raise SystemExit(1)
    record = metadata(directory)
    record['assets'] = [dict(name=p.name, size=p.stat().st_size,
        digest='sha256:' + hashlib.sha256(p.read_bytes()).hexdigest())
        for p in directory.iterdir() if p.name != 'release.json']
    print(json.dumps(record))
elif a[0] == 'api' and '/actions/runs/' in a[1]:
    print(json.dumps(dict(id=4242, event='schedule', head_branch='dev',
        head_sha=os.environ['GITHUB_SHA'], path='.github/workflows/lean-cache-publish.yml',
        status='completed', conclusion='success', repository=dict(full_name='fixture/cache'))))
elif a[0] == 'api' and '/contents/lake-manifest.json?ref=' in a[1]:
    content = (root.parent / 'lake-manifest.json').read_bytes()
    print(json.dumps(dict(type='file', path='lake-manifest.json', encoding='base64',
        content=base64.b64encode(content).decode(), size=len(content),
        sha=hashlib.sha1(b'blob ' + str(len(content)).encode() + b'\\0' + content).hexdigest())))
else:
    raise SystemExit('unexpected transport call: ' + repr(a))
''')
        (self.root / 'bin/gh').chmod(0o755)

    def release_run(self, verb, success=True):
        result = self.guarded_command(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
            verb, '--repository', str(self.root)], cwd=self.root.parent, env=self.env)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        return result

    def test_release_publisher_legacy_seed_current_pack_restore_and_unchanged(self):
        self.release_fixture()
        self.run_lake('build')
        address = json.loads(self.release_run('address').stdout)
        toolchain = (self.root / 'lean-toolchain').read_text().strip()
        slug = ''.join(c if c.isascii() and c.isalnum() else '-' for c in toolchain)
        legacy = 'lean-cache-v1-' + slug + '-' + 'b' * 16 + '-' + 'c' * 16
        directory = self.root / 'releases' / legacy
        directory.mkdir()
        archive = directory / 'lean-build.tgz'
        self.run_lake('pack', str(archive))
        system, machine = address['partition'].split('/')[1].split('-', 1)
        (directory / 'manifest.txt').write_text(''.join(f'{k}={v}\n' for k, v in dict(
            tag=legacy, toolchain=toolchain, os=system, arch=machine, asset='lean-build.tgz',
            config_sha256='b' * 64, sources_sha256='c' * 64,
            archive_sha256=publication.digest(archive), archive_bytes=archive.stat().st_size,
            producer_commit_sha=self.env['GITHUB_SHA'], workflow_run_id='4242').items()))
        (directory / 'release.json').write_text(json.dumps(dict(tag_name=legacy, draft=False,
            target_commitish=self.env['GITHUB_SHA'], published_at='fixture')))
        shutil.rmtree(self.root / '.lake/build')
        restored = self.release_run('fetch')
        self.assertIn('"resolved":"' + legacy + '"', restored.stdout)
        self.assertFalse((self.root / '.lake/build/lean-inspector/report.zip').exists())
        first = self.guarded_command(['make', 'lean-cache-to-github-without-mathlib'], env=self.env)
        self.assertEqual(first.returncode, 0, first.stdout + first.stderr)
        self.assertIn('"status":"published"', first.stdout)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=4 aggregates=1', first.stdout)
        self.assertFalse((self.root / 'unexpected.json').exists(), 'publisher fixes its canonical output')
        output = self.root / '.lake/build/stratalint/raw-lean-report.json'
        expected = {suffix: publication.member(output, suffix).read_bytes() for suffix in publication.SUFFIXES}
        publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        stamps, origins = self.stamps(), self.origins()
        tag = address['release_prefix'] + '4242-1'
        manifest = json.loads((self.root / 'releases' / tag / 'manifest.json').read_text())
        self.assertEqual(address['partition'], manifest['partition'])
        release = json.loads((self.root / 'releases' / tag / 'release.json').read_text())
        self.assertEqual('main', release['target_commitish'])
        self.assertEqual(self.env['GITHUB_SHA'], manifest['producer_commit_sha'])
        self.assertEqual('4242', manifest['workflow_run_id'])
        self.assertEqual('1', manifest['workflow_run_attempt'])
        shutil.rmtree(self.root / '.lake/build')
        restored = self.release_run('fetch')
        self.assertIn('"resolved":"' + tag + '"', restored.stdout)
        self.assertEqual(expected, {suffix: publication.member(output, suffix).read_bytes()
            for suffix in publication.SUFFIXES})
        publication.validate_bundle(output, publication.coordinates(self.root), self.root)
        self.assertTrue((self.root / '.lake/build/lean-inspector/report.zip').is_file())
        self.assertTrue((self.root / '.lake/build/lean-inspector/producer/bin/reportInspector').is_file())
        restored_stamps = self.stamps()
        self.env['GITHUB_RUN_ID'] = '4243'
        unchanged = self.release_run('publish')
        self.assertIn('"status":"published"', unchanged.stdout)
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', unchanged.stdout)
        self.assertEqual(restored_stamps, self.stamps())
        self.assertEqual({k: v[1] for k, v in stamps.items()}, {k: v[1] for k, v in self.stamps().items()})
        self.assertEqual(origins, self.origins())
        for suffix in publication.SUFFIXES:
            actual = publication.member(output, suffix).read_bytes()
            if suffix == '.provenance.json':
                provenance = json.loads(expected[suffix])
                provenance['mode'] = 'cached'
                self.assertEqual(provenance, json.loads(actual))
            else:
                self.assertEqual(expected[suffix], actual)
        releases = {p.name for p in (self.root / 'releases').iterdir()}
        # Even an already published run cannot bypass ordinary default builds.
        self.write('Audit.lean', 'this is not valid Lean\n')
        failed = self.release_run('publish', success=False)
        self.assertIn('LEAN_INSPECTOR_FAILED phase=report', failed.stderr)
        self.assertNotIn('LEAN_CACHE_PUBLISH ', failed.stdout)
        self.assertEqual(releases, {p.name for p in (self.root / 'releases').iterdir()})
        self.write('Audit.lean', 'def audit : Nat := 1\n')
        validator = self.root / 'tools/lean-inspector/publication.py'
        validator.write_text(validator.read_text() + '\ndef validate_bundle(*args, **kwargs):\n'
            + '    raise ValueError("fixture required report validation failed")\n')
        rejected = self.release_run('publish', success=False)
        self.assertIn('fixture required report validation failed', rejected.stdout + rejected.stderr)
        self.assertNotIn('LEAN_CACHE_PUBLISH ', rejected.stdout)
        self.assertEqual(releases, {p.name for p in (self.root / 'releases').iterdir()})
        self.record_result('publication', dict(restored_bundle_parity=True,
            unchanged_extracted_modules=0, unchanged_aggregates=0,
            required_default_failure_exit=failed.returncode, required_validation_failure_exit=rejected.returncode,
            partition=address['partition']))

    def test_release_partition_preserves_semantic_and_selection_changes(self):
        self.release_fixture()
        before = json.loads(self.release_run('address').stdout)
        policy = json.loads((self.root / 'lean-report-inputs.json').read_text())
        policy['report_semantic_version'] += 1
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.assertEqual(before, json.loads(self.release_run('address').stdout))
        policy['report_modules']['exclude'] = ['D5/Alone.lean']
        self.write('lean-report-inputs.json', json.dumps(policy))
        self.assertEqual(before, json.loads(self.release_run('address').stdout))
        self.assertFalse((self.root / '.lake').exists(), 'addressing must preserve cold donor eligibility')
        (self.root / 'tools/lean-inspector/materials.py').unlink()
        failed = self.release_run('publish', success=False)
        self.assertNotIn('LEAN_CACHE_PUBLISH ', failed.stdout)
        self.assertFalse((self.root / 'releases').exists())
