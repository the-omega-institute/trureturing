"""Local make entry guards and explicit build policies at real process boundaries."""
import json
import hashlib
import os
from pathlib import Path
import shutil
import shlex
import subprocess
import sys
import tarfile
import unittest
from unittest.mock import patch
import zipfile

import test_reuse

ROOT = test_reuse.ROOT
import publication

INCOMPLETE_INPUTS = (
    'eligible', 'files', 'execution', 'files:D5/A.lean:sha256', 'files:D5/A.lean:mode',
    'execution:toolchain', 'execution:tools', 'execution:platform', 'execution:environment',
    'execution:platform:system', 'execution:platform:machine',
    *(f'execution:environment:{name}' for name in test_reuse.EXECUTION['environment']),
)
DAMAGED_BUNDLES = ('bundle-empty', 'bundle-member-missing', 'bundle-digest-wrong', 'bundle-bytes-changed')


from test_seed_generation import SeedGenerationTests
from test_local_entry_release import LocalEntryReleaseCases


class LocalEntryFixture:
    def setUp(self):
        self.fixture = test_reuse.ReuseTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        # Coordinate preimages contain compatibility and ordered source/config
        # file digests, never the fixture's absolute path. Verify that projection
        # for every fresh setup; reuse only the scalar used to create its seed.
        inputs = publication.selection.Selection(self.root)
        inputs.validate('lean-report')
        groups = tuple(tuple(inputs.expand(group)) for group in ('report_modules', 'config_inputs'))
        files = tuple((name, publication.digest(inputs.safe_file(name)))
                      for name in sorted({name for group in groups for name in group}))
        key = inputs.compatibility(), groups, files
        initial = getattr(type(self), '_initial_seed_coordinates', None)
        if initial is None or initial[0] != key:
            initial = key, publication.coordinates(self.root)
            type(self)._initial_seed_coordinates = initial
        with patch.object(publication, 'coordinates', return_value=dict(initial[1])):
            self.api = self.fixture.receipt()
        self.seed = self.fixture.report
        self.output = self.root / '.lake/build/stratalint' / publication.RAW
        for name in ('Makefile', 'tools/scripts/report/lean-report.sh',
                     'tools/lean-inspector/inspect.sh', 'tools/lean-inspector/reuse.py',
                     'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                     'tools/lean-inspector/fib_analysis.py',
                     'tools/lean-inspector/native.py',
                     'tools/lean-inspector/build_work.py', 'tools/scripts/lib/resource-observation-lib.sh',
                     'tools/scripts/worktree/lean_cache_release.py', 'tools/scripts/worktree/lean_cache_topology.py',
                     'tools/scripts/worktree/lean_cache.py', 'tools/scripts/worktree/cache_material.py'):
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(ROOT / name, target)
        self.restore = self.root / 'dev-seed'
        shutil.copytree(self.seed.parent, self.restore)
        self.script('tools/scripts/worktree/lean-cache-publish.sh',
                    'printf "fetch %s\\n" "$*" >> calls\n'
                    'exit 1\n')
        self.script('tools/scripts/worktree/lean-cache-ensure.sh',
                    'printf "ensure\\n" >> calls\nmkdir -p .lake\n')
        self.script('tools/scripts/worktree/lean-cache-run.sh',
                    'printf "lake %s\\n" "$*" >> calls\nexit 23\n')
        producer = self.root / 'producer.dll'
        producer.touch()
        self.environment = dict(os.environ, GITHUB_ACTIONS='false', LAKE_BIN=str(self.fixture.lake),
            PATH=str(Path(sys.executable).parent) + os.pathsep + os.environ['PATH'],
            STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_PRODUCER_DLL=str(producer),
            STRATALINT_LEAN_REPORT_REUSE=str(self.seed), STRATALINT_LEAN_BUILD_TARGETS='[]',
            STRATALINT_LEAN_REPORT_LOG_DIR=str(self.root / 'logs'))
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True, capture_output=True)
        self.fixture.write('.gitignore', '.lake/\nbin/\nseed/\ndev-seed/\nlogs/\ncalls\n'
                           'producer.dll\nrelease-manifest.json\nreleases/\nlake-manifest.json\ncustom-output/\n'
                           '__pycache__/\nbuild/\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'Makefile', 'tools', 'D5',
                        'Audit.lean', 'Inspector.lean', 'producer.py', 'lean-toolchain',
                        'lakefile.toml', 'lean-report-inputs.json', '.gitignore'], check=True, capture_output=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Fixture',
                        '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                        'commit', '-qm', 'local report fixture'], check=True, capture_output=True)

    def linked_checkout(self):
        self.main_checkout = self.root.resolve()
        linked = self.root / 'linked checkout'
        subprocess.run(['git', '-C', str(self.root), 'worktree', 'add', '--detach',
                        str(linked), 'HEAD'], check=True, capture_output=True)
        shutil.copytree(self.seed.parent, linked / 'seed')
        self.root = linked.resolve()
        self.seed = self.root / 'seed' / publication.RAW
        self.output = self.root / '.lake/build/stratalint' / publication.RAW
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(self.seed)

    def separate_git_directory(self):
        store = self.root / 'repository store' / 'git directory'
        store.parent.mkdir()
        subprocess.run(['git', 'init', '-q', '--separate-git-dir', str(store), str(self.root)],
                       check=True, capture_output=True)
        self.git_store = store.resolve()

    def assert_linked_guarded(self, kind, unknown_main=False):
        self.linked_checkout()
        self.damage(kind)
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(result.returncode, 4, '[FAIL] linked_miss_returns_status_4: '
                         + result.stdout + result.stderr)
        diagnostic = result.stdout + result.stderr
        self.assertIn('reason=linked-worktree', diagnostic, '[FAIL] linked_miss_names_policy')
        remediation = ('sync dev and warm the dev cache in this repository\'s dev main checkout: '
                       'make warm-donor && make lean-report there '
                       '(its location cannot be determined from this worktree); then reseed: rm -rf -- '
                       + shlex.quote(str(self.root / '.lake')) + ' && make -C '
                       + shlex.quote(str(self.root)) + ' lean-cache-ensure'
                       if unknown_main else 'sync dev and warm the dev cache: make -C '
                      + shlex.quote(str(self.main_checkout)) + ' warm-donor && make -C '
                      + shlex.quote(str(self.main_checkout)) + ' lean-report'
                      + '; then reseed from the warm main checkout: rm -rf -- '
                      + shlex.quote(str(self.root / '.lake')) + ' && make -C '
                      + shlex.quote(str(self.root)) + ' lean-cache-ensure')
        self.assertIn(remediation, diagnostic,
                      '[FAIL] linked_remediation_builds_main_report_before_reseed')
        if unknown_main:
            self.assertNotIn(str(self.git_store), diagnostic,
                             '[FAIL] linked_remediation_never_names_git_store')
        self.assertIn('rm -rf -- ' + shlex.quote(str(self.root / '.lake'))
                      + ' && make -C ' + shlex.quote(str(self.root)) + ' lean-cache-ensure', diagnostic)
        self.assertNotIn('lean-cache-from-github-without-mathlib', diagnostic)
        self.assertEqual(self.calls, [], '[FAIL] linked_miss_never_fetches_or_builds')
        self.assertFalse((self.root / '.lake').exists())

    def assert_canonical_seed_published(self, destination, result):
        self.assertEqual(result.returncode, 0,
                         '[FAIL] linked_canonical_seed_publishes_custom_output: '
                         + result.stdout + result.stderr)
        self.assertEqual(self.calls, [], '[FAIL] linked_canonical_reuse_never_fetches_or_builds')
        self.assertIn('complete-entry-reused', result.stdout)
        self.assertEqual(destination.read_bytes(), self.output.read_bytes())
        publication.validate_bundle(destination, publication.coordinates(self.root), self.root)
        self.assertFalse(self.api.probe(self.root, destination)['needs_lake'],
                         '[FAIL] custom_publication_has_current_reuse_receipt')
        self.assertEqual(json.loads(publication.member(destination, '.provenance.json').read_text())['mode'],
                         'cached')

    def script(self, name, body):
        target = self.root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text('#!/bin/bash\nset -euo pipefail\n' + body)
        target.chmod(0o755)

    def run_entry(self, *options, direct=False):
        command = (['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
                    '--repository', str(self.root), '--output', str(self.output), *options]
                   if direct else ['make', '--no-print-directory', 'lean-report', *options])
        result = subprocess.run(command, cwd=self.root, env=self.environment,
                                text=True, capture_output=True, timeout=30)
        self.calls = ((self.root / 'calls').read_text().splitlines()
                      if (self.root / 'calls').exists() else [])
        return result

    def damage(self, kind):
        receipt = publication.member(self.seed, '.reuse.json')
        if kind == 'missing':
            shutil.rmtree(self.seed.parent)
        elif kind == 'receipt-missing':
            receipt.unlink()
        elif kind == 'member-missing':
            publication.member(self.seed, '.materials.zip').unlink()
        elif kind == 'invalid':
            receipt.write_text('invalid JSON')
        elif kind == 'incomplete':
            record = json.loads(receipt.read_text())
            record['completed'] = ['report']
            receipt.write_text(json.dumps(record))
        elif kind == 'format':
            record = json.loads(receipt.read_text())
            record['inputs']['report_format'] = 'incompatible-report-format'
            receipt.write_text(json.dumps(record))
        elif kind.startswith('inputs-without:'):
            record = json.loads(receipt.read_text())
            fields = kind.split(':', 1)[1].split(':')
            target = record['inputs']
            for field in fields[:-1]:
                target = target[field]
            del target[fields[-1]]
            receipt.write_text(json.dumps(record))
        elif kind.startswith('bundle-'):
            record = json.loads(receipt.read_text())
            if kind == 'bundle-empty':
                record['bundle'] = {}
            elif kind == 'bundle-member-missing':
                del record['bundle']['.materials.zip']
            elif kind == 'bundle-digest-wrong':
                record['bundle']['.materials.zip'] = '0' * 64
            elif kind == 'bundle-bytes-changed':
                publication.member(self.seed, '.materials.zip').write_bytes(b'corrupt')
            receipt.write_text(json.dumps(record))

    def restore_seed(self):
        self.script('tools/scripts/worktree/lean-cache-publish.sh',
                    'printf "fetch %s\\n" "$*" >> calls\n'
                    'mkdir -p .lake/build/stratalint\n'
                    'cp dev-seed/* .lake/build/stratalint/\n')

    def write_base(self, commit):
        if not self.output.exists():
            shutil.copytree(self.seed.parent, self.output.parent, dirs_exist_ok=True)
        path = self.root / '.lake/lean-report-seed-base.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({
            'schema': self.api.BASE_SCHEMA,
            'producer_commit_sha': commit,
            'seed_sha256': self.api.seed_identity(self.output),
        }) + '\n')

    def git_commit(self, message, *, empty=False):
        command = ['git', '-C', str(self.root), '-c', 'user.name=Fixture',
                   '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                   'commit']
        if empty:
            subprocess.run([*command, '--allow-empty', '-qm', message],
                           check=True, capture_output=True)
        else:
            subprocess.run(['git', '-C', str(self.root), 'add', '-A'], check=True, capture_output=True)
            subprocess.run([*command, '-qm', message],
                           check=True, capture_output=True)
        return subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()

    def inject_restore_error(self, operation):
        site = self.root / '.lake/injection'
        site.mkdir(exist_ok=True)
        (site / 'sitecustomize.py').write_text('''import os, pathlib, shutil
replace, rmtree = os.replace, shutil.rmtree
rename = pathlib.Path.rename
def failed_replace(source, target):
    if pathlib.Path(target).name == 'lean-report-seed-base.json':
        raise OSError('injected base write failure')
    return replace(source, target)
def failed_cleanup(path, *args, **kwargs):
    name = pathlib.Path(path).name
    if name.startswith(os.environ.get('FAKE_CLEANUP_PREFIX', 'no-match')):
        raise OSError('injected cleanup failure')
    return rmtree(path, *args, **kwargs)
def failed_rollback(self, target):
    if (os.environ.get('FAKE_ROLLBACK_FAILURE') == '1'
            and self.name == 'build' and self.parent.name.startswith('.release-backup-')
            and pathlib.Path(target).name == 'build'):
        raise OSError('injected rollback rename failure')
    return rename(self, target)
if os.environ.get('FAKE_BASE_WRITE_FAILURE') == '1':
    os.replace = failed_replace
shutil.rmtree = failed_cleanup
pathlib.Path.rename = failed_rollback
''')
        self.environment['PYTHONPATH'] = str(site)
        if operation == 'base':
            self.environment['FAKE_BASE_WRITE_FAILURE'] = '1'
        elif operation == 'rollback':
            self.environment['FAKE_ROLLBACK_FAILURE'] = '1'
            self.environment['FAKE_CLEANUP_PREFIX'] = '.release-'
        else:
            self.environment['FAKE_CLEANUP_PREFIX'] = operation

class LocalEntryTests(LocalEntryFixture, SeedGenerationTests, LocalEntryReleaseCases, unittest.TestCase):
    def test_linked_missing_seed_refuses_without_fetch_or_lake(self):
        self.assert_linked_guarded('missing')

    def test_linked_format_mismatch_refuses_without_fetch_or_lake(self):
        self.assert_linked_guarded('format')

    def test_linked_damaged_seed_refuses_without_fetch_or_lake(self):
        self.assert_linked_guarded('bundle-bytes-changed')

    def test_linked_incomplete_seed_refuses_without_fetch_or_lake(self):
        self.assert_linked_guarded('incomplete')

    def test_separate_git_dir_linked_report_refusal_omits_unvalidated_main_checkout(self):
        self.separate_git_directory()
        self.assert_linked_guarded('missing', unknown_main=True)

    def test_separate_git_dir_main_report_recovery_still_fetches(self):
        self.separate_git_directory()
        self.damage('missing')
        self.restore_seed()
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(len(self.calls), 1, '[FAIL] separate_git_dir_main_fetches_report')
        self.assertTrue(self.calls[0].startswith('fetch fetch --mode production'))
        self.assertIn('complete-entry-reused', result.stdout)

    def test_linked_explicit_rebuild_never_fetches(self):
        self.linked_checkout()
        self.damage('format')
        result = self.run_entry('REBUILD_REPORT_CACHE=1')
        self.assertNotIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stdout + result.stderr)
        self.assertEqual(len(self.calls), 2)
        self.assertEqual(self.calls[0], 'ensure')
        self.assertIn('build :report', self.calls[1])

    def test_linked_reuse_or_build_never_fetches(self):
        self.linked_checkout()
        self.damage('format')
        result = self.run_entry('--cache-miss-policy', 'reuse-or-build', direct=True)
        self.assertNotIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stdout + result.stderr)
        self.assertEqual(len(self.calls), 2)
        self.assertEqual(self.calls[0], 'ensure')
        self.assertIn('build :report', self.calls[1])

    def test_linked_matching_seed_reuses_without_fetch_or_lake(self):
        self.linked_checkout()
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('complete-entry-reused', result.stdout)
        self.assertEqual(self.calls, [])

    def test_linked_custom_output_reuses_canonical_seed_without_fetch_or_lake(self):
        self.linked_checkout()
        shutil.copytree(self.seed.parent, self.output.parent)
        self.environment.pop('STRATALINT_LEAN_REPORT_REUSE')
        destination = self.root / 'custom output/report.json'
        self.assertFalse(destination.exists())
        result = self.run_entry('LEAN_REPORT=' + str(destination))
        self.assert_canonical_seed_published(destination, result)

    def test_linked_unusable_selected_seed_reuses_canonical_without_fetch_or_lake(self):
        for kind in ('missing', 'incomplete', 'bundle-bytes-changed', 'format'):
            with self.subTest(kind=kind):
                self.setUp()
                self.linked_checkout()
                shutil.copytree(self.seed.parent, self.output.parent)
                self.damage(kind)
                destination = self.root / 'custom output/report.json'
                result = self.run_entry('LEAN_REPORT=' + str(destination))
                self.assert_canonical_seed_published(destination, result)

    def test_linked_custom_output_refuses_unusable_canonical_without_fetch_or_lake(self):
        for kind in ('missing', 'incomplete', 'bundle-bytes-changed', 'format'):
            with self.subTest(kind=kind):
                self.setUp()
                self.linked_checkout()
                shutil.copytree(self.seed.parent, self.output.parent)
                self.seed = self.output
                self.damage(kind)
                self.environment.pop('STRATALINT_LEAN_REPORT_REUSE')
                destination = self.root / 'custom output/report.json'
                result = self.run_entry('LEAN_REPORT=' + str(destination))
                self.assertNotEqual(result.returncode, 0,
                                    '[FAIL] unusable_canonical_must_refuse_custom_output')
                self.assertIn('reason=linked-worktree', result.stdout + result.stderr)
                self.assertEqual(self.calls, [], '[FAIL] unusable_canonical_never_fetches_or_builds')
                self.assertFalse(destination.exists())

    def test_undetermined_checkout_refuses_without_fetch_or_lake(self):
        self.damage('missing')
        self.script('bin/git', 'echo "topology unavailable" >&2\nexit 17\n')
        self.environment['PATH'] = str(self.root / 'bin') + os.pathsep + self.environment['PATH']
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(result.returncode, 4, result.stdout + result.stderr)
        self.assertIn('reason=checkout-undetermined', result.stdout + result.stderr)
        self.assertIn('topology unavailable', result.stdout + result.stderr)
        self.assertEqual(self.calls, [], '[FAIL] unknown_checkout_never_fetches_or_builds')

    def test_history_fixture_commits_without_ambient_identity_or_signing(self):
        global_config = self.root / '.git/fixture-global.config'
        global_config.write_text('[user]\n\tuseConfigOnly = true\n[commit]\n\tgpgsign = true\n')
        environment = dict(os.environ, GIT_CONFIG_GLOBAL=str(global_config),
                           GIT_CONFIG_SYSTEM='/dev/null', GIT_CONFIG_COUNT='0')
        for name in ('GIT_AUTHOR_NAME', 'GIT_AUTHOR_EMAIL', 'GIT_COMMITTER_NAME',
                     'GIT_COMMITTER_EMAIL', 'EMAIL', 'GIT_CONFIG_PARAMETERS'):
            environment.pop(name, None)
        with patch.dict(os.environ, environment, clear=True):
            for empty in (True, False):
                with self.subTest(empty=empty):
                    if not empty:
                        self.fixture.write('D5/A.lean', 'def a := 2\n')
                    try:
                        self.git_commit('isolated fixture history', empty=empty)
                    except subprocess.CalledProcessError as error:
                        self.fail('[FAIL] fixture_history_commit_is_independent_of_ambient_git: '
                                  + error.stderr.decode())
                    identity = subprocess.check_output(
                        ['git', '-C', str(self.root), 'log', '-1', '--format=%an <%ae>|%cn <%ce>'],
                        text=True).strip()
                    self.assertEqual(identity,
                        'Fixture <fixture@example.invalid>|Fixture <fixture@example.invalid>',
                        '[FAIL] fixture_history_uses_fixture_author_and_committer')



if __name__ == '__main__':
    unittest.main()
