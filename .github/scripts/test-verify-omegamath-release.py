"""Check the consumer's release acceptance boundary without fetching packages."""
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import call, patch


verifier_path = Path(__file__).with_name('verify-omegamath-release.py')
spec = importlib.util.spec_from_file_location('verify_omegamath_release', verifier_path)
verifier = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verifier)


class ReleaseTest(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        self.root = Path(tmp.name)
        self.package = self.root / '.lake/packages/omegamath'
        self.archive = self.package / '.lake/omegamath-test.tar.gz'
        self.archive.parent.mkdir(parents=True)
        self.archive.write_bytes(b'test build archive')
        sha = 'd' * 40
        self.lean_toolchain = 'leanprover/lean4:v4.35.0'
        repository = 'the-omega-institute/omegamath'
        manifest = {'packagesDir': '.lake/packages', 'packages': [
            {'name': 'omegamath', 'url': 'https://github.com/' + repository, 'rev': sha}]}
        receipt = {'source': sha, 'repository': repository, 'toolchain': self.lean_toolchain,
                   'assets': {self.archive.name: 'sha256:' + hashlib.sha256(self.archive.read_bytes()).hexdigest()}}
        (self.root / 'Reg').mkdir()
        (self.root / 'Meta').mkdir()
        for path in ('lake-manifest.json', 'Reg/lake-manifest.json'):
            (self.root / path).write_text(json.dumps(manifest))
        (self.root / 'Meta/omegamath-release.json').write_text(json.dumps(receipt))
        (self.root / 'lean-toolchain').write_text(self.lean_toolchain)
        processes = patch.object(verifier, 'subprocess', autospec=True)
        self.commands = processes.start()
        self.addCleanup(processes.stop)
        self.commands.check_output.side_effect = [sha + '\n', self.archive.name + '\n', 'v0.1.0-rc.1\n']
        downloads = patch.object(verifier, 'urlopen', autospec=True)
        self.download = downloads.start()
        self.addCleanup(downloads.stop)
        self.expected = self.archive.read_bytes()

    def test_cached_archive_installs_and_checks_all_public_targets(self):
        verifier.verify_release(self.root)
        self.download.assert_not_called()
        self.assertEqual(self.commands.run.call_args_list, [
            call(['lake', 'env', 'true'], cwd=self.root, check=True),
            call(['tar', '-xzf', self.archive, '-C', self.package / '.lake/build'], check=True),
            call(['lake', '--no-cache', '--no-build', 'build', '@omegamath/OmegaInit',
                  '@omegamath/OmegaMathlib', '@omegamath/OmegaMath', '@omegamath/OmegaBuild',
                  '@omegamath/omegaBackendPlan'], cwd=self.root, check=True),
        ])

    def test_fetches_verified_archive_when_cached_pin_changed(self):
        self.archive.write_bytes(b'older build')
        self.download.return_value = io.BytesIO(self.expected)
        verifier.verify_release(self.root)
        self.assertEqual(self.archive.read_bytes(), self.expected)
        self.download.assert_called_once_with(
            'https://github.com/the-omega-institute/omegamath/releases/download/v0.1.0-rc.1/'
            + self.archive.name, timeout=120)

    def test_mismatched_release_is_never_extracted(self):
        self.archive.unlink()
        self.download.return_value = io.BytesIO(b'different bytes')
        with self.assertRaisesRegex(ValueError, 'has digest'):
            verifier.verify_release(self.root)
        self.commands.run.assert_called_once_with(['lake', 'env', 'true'], cwd=self.root, check=True)
        self.assertFalse(self.archive.exists())
        self.assertFalse((self.package / '.lake/build').exists())

    def test_reg_must_resolve_the_same_release(self):
        path = self.root / 'Reg/lake-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['packages'][0]['rev'] = 'e' * 40
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'pinned source in root or Reg'):
            verifier.verify_release(self.root)
        self.commands.run.assert_not_called()


if __name__ == '__main__':
    unittest.main()
