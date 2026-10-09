"""Local make entry guards and explicit build policies at real process boundaries."""
import json
import os
from pathlib import Path
import shutil
import shlex
import subprocess
import sys
import unittest

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


class LocalEntryTests(unittest.TestCase):
    def setUp(self):
        self.fixture = test_reuse.ReuseTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.api = self.fixture.receipt()
        self.seed = self.fixture.report
        self.output = self.root / '.lake/build/stratalint' / publication.RAW
        for name in ('Makefile', 'tools/scripts/report/lean-report.sh',
                     'tools/lean-inspector/inspect.sh', 'tools/lean-inspector/reuse.py',
                     'tools/lean-inspector/publication.py', 'tools/lean-inspector/materials.py',
                     'tools/lean-inspector/build_work.py', 'tools/scripts/lib/resource-observation-lib.sh',
                     'tools/scripts/worktree/lean_cache_release.py',
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
        self.environment = dict(os.environ, LAKE_BIN=str(self.fixture.lake),
            PATH=str(Path(sys.executable).parent) + os.pathsep + os.environ['PATH'],
            STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_PRODUCER_DLL=str(producer),
            STRATALINT_LEAN_REPORT_REUSE=str(self.seed), STRATALINT_LEAN_BUILD_TARGETS='[]',
            STRATALINT_LEAN_REPORT_LOG_DIR=str(self.root / 'logs'))
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True, capture_output=True)
        subprocess.run(['git', '-C', str(self.root), 'add', 'Makefile', 'tools', 'D5',
                        'Audit.lean', 'Inspector.lean', 'producer.py', 'lean-toolchain',
                        'lakefile.toml', 'lean-report-inputs.json'], check=True, capture_output=True)
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

    def assert_guarded(self, result):
        self.assertNotEqual(result.returncode, 0, '[FAIL] incompatible_entry_must_fail')
        self.assertIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stdout + result.stderr,
                      '[FAIL] incompatible_entry_names_diagnostic')
        self.assertIn('REBUILD_REPORT_CACHE=1', result.stdout + result.stderr)
        self.assertEqual(len(self.calls), 1, '[FAIL] local_miss_only_fetches_before_failure')
        self.assertTrue(self.calls[0].startswith('fetch fetch --mode production'))
        self.assertIn('--refresh-stale', self.calls[0])
        self.assertNotIn('phase=report ', result.stderr, '[FAIL] incompatible_entry_never_extracts')

    def test_missing_seed_fetches_then_fails_without_lake(self):
        self.damage('missing')
        self.assert_guarded(self.run_entry())
        self.assertFalse((self.root / '.lake').exists())

    def test_format_mismatch_fetches_then_fails_without_lake(self):
        self.damage('format')
        self.assert_guarded(self.run_entry())

    def test_incomplete_or_invalid_seed_cannot_enable_full_build(self):
        for kind in ('receipt-missing', 'member-missing', 'invalid', 'incomplete'):
            with self.subTest(kind=kind):
                self.setUp()
                self.damage(kind)
                self.assert_guarded(self.run_entry())

    def test_fetched_seed_still_incompatible_fails_before_lake(self):
        self.damage('format')
        shutil.rmtree(self.restore)
        shutil.copytree(self.seed.parent, self.restore)
        self.restore_seed()
        self.assert_guarded(self.run_entry())

    def test_incomplete_local_seed_recovers_before_reuse(self):
        for field in INCOMPLETE_INPUTS:
            with self.subTest(field=field):
                self.setUp()
                self.damage('inputs-without:' + field)
                self.restore_seed()
                result = self.run_entry()
                self.assertEqual(result.returncode, 0,
                                 '[FAIL] incomplete_local_seed_recovery_must_succeed: '
                                 + result.stdout + result.stderr)
                self.assertEqual(len(self.calls), 1, '[FAIL] incomplete_local_seed_must_recover')
                self.assertTrue(self.calls[0].startswith('fetch '))
                self.assertIn('complete-entry-reused', result.stdout)

    def test_incomplete_restored_seed_fails_before_lake(self):
        for field in INCOMPLETE_INPUTS:
            with self.subTest(field=field):
                self.setUp()
                self.damage('inputs-without:' + field)
                shutil.rmtree(self.restore)
                shutil.copytree(self.seed.parent, self.restore)
                self.damage('missing')
                self.restore_seed()
                self.assert_guarded(self.run_entry())

    def test_damaged_local_bundle_recovers_before_reuse(self):
        for kind in DAMAGED_BUNDLES:
            with self.subTest(kind=kind):
                self.setUp()
                self.damage(kind)
                self.restore_seed()
                result = self.run_entry()
                self.assertEqual(result.returncode, 0,
                                 '[FAIL] damaged_local_bundle_recovery_must_succeed: '
                                 + result.stdout + result.stderr)
                self.assertEqual(len(self.calls), 1, '[FAIL] damaged_local_bundle_must_recover')
                self.assertTrue(self.calls[0].startswith('fetch '))
                self.assertIn('complete-entry-reused', result.stdout)

    def test_damaged_restored_bundle_fails_before_lake(self):
        for kind in DAMAGED_BUNDLES:
            with self.subTest(kind=kind):
                self.setUp()
                self.damage(kind)
                shutil.rmtree(self.restore)
                shutil.copytree(self.seed.parent, self.restore)
                self.damage('missing')
                self.restore_seed()
                self.assert_guarded(self.run_entry())

    def test_fetched_matching_seed_reuses_complete_report(self):
        self.damage('missing')
        self.restore_seed()
        result = self.run_entry()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(len(self.calls), 1, '[FAIL] fetched_matching_seed_must_skip_report_build')
        self.assertIn('LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0', result.stdout)
        self.assertTrue(publication.member(self.output, '.reuse.json').is_file())

    def test_fetched_matching_format_with_changed_inputs_uses_incremental_entry(self):
        self.damage('format')
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        self.restore_seed()
        result = self.run_entry()
        self.assertNotEqual(result.returncode, 0)  # Native build stub preserves failure.
        self.assertNotIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stdout + result.stderr,
                         '[FAIL] matching_restored_format_must_allow_incremental_build')
        self.assertEqual(len(self.calls), 3)
        self.assertEqual(self.calls[1], 'ensure')
        self.assertIn('build :report', self.calls[2], '[FAIL] compatible_fetch_keeps_lake_incremental_path')
        self.assertIn('changed_inputs=1', result.stdout)

    def test_matching_local_seed_with_changed_inputs_does_not_fetch(self):
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        result = self.run_entry()
        self.assertNotIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stdout + result.stderr,
                         '[FAIL] matching_local_format_must_allow_incremental_build')
        self.assertEqual(len(self.calls), 2)
        self.assertEqual(self.calls[0], 'ensure')
        self.assertIn('build :report', self.calls[1])

    def test_same_format_program_changes_preserve_complete_reuse(self):
        self.fixture.write('producer.py', '# changed producer\n')
        result = self.run_entry()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(self.calls, [])
        self.assertIn('extracted_modules=0 aggregates=0', result.stdout)

    def test_rebuild_opt_in_enters_full_path_without_fetch_or_receipt_reuse(self):
        result = self.run_entry('REBUILD_REPORT_CACHE=1')
        self.assertNotEqual(result.returncode, 0, '[FAIL] explicit_build_propagates_lake_failure')
        self.assertEqual(len(self.calls), 2, '[FAIL] explicit_build_must_enter_report_path')
        self.assertEqual(self.calls[0], 'ensure')
        self.assertIn('build :report', self.calls[1])
        self.assertNotIn('complete-entry-reused', result.stdout)

    def test_reuse_or_build_is_explicit_and_never_fetches(self):
        self.damage('format')
        result = self.run_entry('LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build')
        self.assertNotIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stdout + result.stderr,
                         '[FAIL] explicit_reuse_or_build_must_allow_full_path')
        self.assertEqual(len(self.calls), 2)
        self.assertEqual(self.calls[0], 'ensure')
        self.assertIn('build :report', self.calls[1])

    def test_ci_environment_does_not_change_local_policy(self):
        self.damage('missing')
        self.environment['GITHUB_ACTIONS'] = 'true'
        self.assert_guarded(self.run_entry())

    def test_direct_guard_returns_dedicated_status_before_program_builds(self):
        self.damage('format')
        self.environment['STRATALINT_LEAN_BUILD_TARGETS'] = '["Probe"]'
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(result.returncode, 4, '[FAIL] dedicated_guard_status_reaches_direct_caller')
        self.assert_guarded(result)

    def test_invalid_make_options_fail_before_fetch_or_build(self):
        for option in ('REBUILD_REPORT_CACHE=2', 'LEAN_REPORT_CACHE_MISS_POLICY=invalid'):
            result = self.run_entry(option)
            self.assertNotEqual(result.returncode, 0, '[FAIL] invalid_option_must_fail_fast')
            self.assertEqual(self.calls, [])

    def test_custom_output_uses_fetched_canonical_seed(self):
        self.damage('missing')
        self.restore_seed()
        destination = self.root / 'custom/report.json'
        result = self.run_entry('LEAN_REPORT=' + str(destination))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertTrue(destination.is_file(), '[FAIL] fetched_seed_publishes_requested_output')

    def test_refresh_option_reaches_canonical_release_reader(self):
        result = subprocess.run(['make', '--no-print-directory',
                                 'lean-cache-from-github-without-mathlib', 'REFRESH_STALE=1'],
                                cwd=self.root, env=self.environment, text=True, capture_output=True, timeout=30)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn('--refresh-stale', (self.root / 'calls').read_text(),
                      '[FAIL] explicit_refresh_must_replace_existing_build')

    def test_busy_cache_preserves_other_writer_receipt(self):
        sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
        from lean_cache_release import cache_guard
        self.api.reuse(self.root, self.seed, self.output)
        receipt = publication.member(self.output, '.reuse.json')
        before = receipt.read_bytes()
        self.environment.pop('STRATALINT_LEAN_REPORT_REUSE')
        with cache_guard(self.root):
            result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(result.returncode, 4)
        self.assertEqual(self.calls, [])
        self.assertTrue(receipt.is_file(), '[FAIL] busy_guard_must_preserve_other_writer_receipt')
        self.assertEqual(receipt.read_bytes(), before)


if __name__ == '__main__':
    unittest.main()
