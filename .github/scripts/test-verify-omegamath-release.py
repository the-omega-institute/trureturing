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
        self.archive = self.package / '.lake/omegamath-arm64-apple-darwin24.6.0.tar.gz'
        self.archive.parent.mkdir(parents=True)
        self.archive.write_bytes(b'test build archive')
        sha = 'd' * 40
        self.lean_toolchain = 'leanprover/lean4:v4.35.0'
        repository = 'the-omega-institute/omegamath'
        manifest = {'packagesDir': '.lake/packages', 'packages': [
            {'name': 'omegamath', 'url': 'https://github.com/' + repository, 'rev': sha},
            {'name': 'mathlib', 'inherited': False, 'rev': 'a' * 40}]}
        (self.package / 'lake-manifest.json').write_text(json.dumps({'packages': []}))
        (self.package / 'lakefile.toml').write_text('name = "omegamath"\n')
        receipt = {'source': sha, 'repository': repository, 'toolchain': self.lean_toolchain,
                   'assets': {'omegamath-aarch64-unknown-linux-gnu.tar.gz': 'sha256:' + 'a' * 64, self.archive.name: 'sha256:' + hashlib.sha256(self.archive.read_bytes()).hexdigest()}}
        (self.root / 'Reg').mkdir()
        (self.root / 'Meta').mkdir()
        for path in ('lake-manifest.json', 'Reg/lake-manifest.json'):
            (self.root / path).write_text(json.dumps(manifest))
        self.published = receipt
        (self.root / 'Meta/omegamath-release.json').write_text(json.dumps({**receipt, 'tag': 'v0.1.0-rc.1'}))
        (self.root / 'lean-toolchain').write_text(self.lean_toolchain)
        processes = patch.object(verifier, 'subprocess', autospec=True)
        self.commands = processes.start()
        self.addCleanup(processes.stop)
        self.commands.check_output.side_effect = [sha + '\n', self.archive.name + '\n']
        downloads = patch.object(verifier, 'urlopen', autospec=True)
        self.download = downloads.start()
        self.addCleanup(downloads.stop)
        self.expected = self.archive.read_bytes()
        self.archive_bytes = self.expected

        def fetch(url, *, timeout):
            if url.endswith('/omegamath-release.json'):
                return io.BytesIO(json.dumps(self.published).encode())
            return io.BytesIO(self.archive_bytes)
        self.download.side_effect = fetch

    def test_cached_archive_installs_and_checks_all_public_targets(self):
        verifier.verify_release(self.root)
        self.download.assert_called_once_with(verifier.release_url('v0.1.0-rc.1', 'omegamath-release.json'), timeout=120)
        self.assertEqual(self.commands.run.call_args_list, [
            call(['lake', 'env', 'true'], cwd=self.root, check=True),
            call(['tar', '-xzf', self.archive, '-C', self.package / '.lake/build'], check=True),
            call(['lake', '--no-cache', '--no-build', 'build', '@omegamath/OmegaInit',
                  '@omegamath/OmegaMathlib', '@omegamath/OmegaMath', '@omegamath/OmegaBuild',
                  '@omegamath/omegaBackendPlan'], cwd=self.root, check=True),
        ])

    def test_fetches_verified_archive_when_cached_pin_changed(self):
        self.archive.write_bytes(b'older build')
        verifier.verify_release(self.root)
        self.assertEqual(self.archive.read_bytes(), self.expected)
        self.download.assert_called_with(
            'https://github.com/the-omega-institute/omegamath/releases/download/v0.1.0-rc.1/'
            + self.archive.name, timeout=120)

    def test_same_commit_can_select_stable_without_local_tags(self):
        path = self.root / 'Meta/omegamath-release.json'
        pin = json.loads(path.read_text())
        pin['tag'] = 'v0.1.0'
        path.write_text(json.dumps(pin))
        self.archive.unlink()
        verifier.verify_release(self.root)
        self.assertEqual(self.download.call_args_list, [
            call(verifier.release_url('v0.1.0', name), timeout=120)
            for name in ('omegamath-release.json', self.archive.name)
        ])
        self.assertEqual(self.commands.check_output.call_count, 2)

    def test_other_platform_must_match_the_public_manifest(self):
        self.published['assets']['omegamath-aarch64-unknown-linux-gnu.tar.gz'] = 'sha256:' + 'e' * 64
        with self.assertRaisesRegex(ValueError, 'published manifest'):
            verifier.verify_release(self.root)
        self.assertEqual(self.commands.run.call_count, 1)

    def test_receipt_pins_both_supported_platforms(self):
        path = self.root / 'Meta/omegamath-release.json'
        pin = json.loads(path.read_text())
        del pin['assets']['omegamath-aarch64-unknown-linux-gnu.tar.gz']
        path.write_text(json.dumps(pin))
        with self.assertRaisesRegex(ValueError, 'each supported'):
            verifier.verify_release(self.root)
        self.download.assert_not_called()

    def test_mismatched_release_is_never_extracted(self):
        self.archive.unlink()
        self.archive_bytes = b'different bytes'
        with self.assertRaisesRegex(ValueError, 'has digest'):
            verifier.verify_release(self.root)
        self.commands.run.assert_called_once_with(['lake', 'env', 'true'], cwd=self.root, check=True)
        self.assertFalse(self.archive.exists())
        self.assertFalse((self.package / '.lake/build').exists())

    def test_product_rejects_direct_or_transitive_mathlib(self):
        lock = self.package / 'lake-manifest.json'
        config = self.package / 'lakefile.toml'
        with patch.object(verifier.subprocess, 'check_output', return_value='d' * 40):
            for direct in (True, False):
                with self.subTest(direct=direct):
                    if direct:
                        config.write_text('[[require]]\nname = "mathlib"\n')
                    else:
                        config.write_text('name = "omegamath"\n')
                        lock.write_text(json.dumps({'packages': [{'name': 'mathlib', 'inherited': True}]}))
                    with self.assertRaisesRegex(ValueError, 'product dependencies'):
                        verifier.verify_release(self.root)
        self.download.assert_not_called()

    def test_consumer_must_pin_mathlib_directly(self):
        path = self.root / 'lake-manifest.json'
        manifest = json.loads(path.read_text())
        manifest['packages'][1]['inherited'] = True
        path.write_text(json.dumps(manifest))
        with self.assertRaisesRegex(ValueError, 'directly pin'):
            verifier.verify_release(self.root)
        self.commands.run.assert_not_called()

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
