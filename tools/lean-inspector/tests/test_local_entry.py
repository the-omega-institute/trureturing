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


class LocalEntryTests(SeedGenerationTests, unittest.TestCase):
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
                     'tools/lean-inspector/native.py',
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
        if empty:
            subprocess.run(['git', '-C', str(self.root), 'commit', '--allow-empty', '-qm', message],
                           check=True, capture_output=True)
        else:
            subprocess.run(['git', '-C', str(self.root), 'add', '-A'], check=True, capture_output=True)
            subprocess.run(['git', '-C', str(self.root), 'commit', '-qm', message],
                           check=True, capture_output=True)
        return subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()

    def release_stub(self, producer, *, failure=None):
        sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
        import lean_cache_release
        from lean_cache import partition_path
        cache_key = lean_cache_release.release_key(self.root)
        partition = partition_path(self.root)
        tag = lean_cache_release.prefix(partition, cache_key) + 'local-' + producer[:12] + '-20261010T120000000000Z'
        manifest = self.root / 'release-manifest.json'
        manifest.write_text(json.dumps({
            'schema': 'lean-release-seed-v4', 'partition': partition,
            'cache_key': cache_key, 'producer_commit_sha': producer,
            'publication_id': tag.rsplit('-', 2)[-3] + '-' + tag.rsplit('-', 2)[-2] + '-' + tag.rsplit('-', 2)[-1],
            'archive_sha256': 'a' * 64, 'archive_bytes': 1,
            'parts': [{'name': 'lean-build.tgz', 'sha256': 'a' * 64, 'bytes': 1}],
        }))
        # The publication id is fixed by the tag suffix; use a valid local id.
        manifest_record = json.loads(manifest.read_text())
        manifest_record['publication_id'] = 'local-' + producer[:12] + '-20261010T120000000000Z'
        manifest.write_text(json.dumps(manifest_record))
        digest = __import__('hashlib').sha256(manifest.read_bytes()).hexdigest()
        self.environment['FAKE_RELEASE_TAG'] = tag
        self.environment['FAKE_RELEASE_MANIFEST'] = str(manifest)
        self.environment['FAKE_RELEASE_MANIFEST_DIGEST'] = digest
        self.environment['FAKE_RELEASE_FAILURE'] = failure or ''
        self.script('bin/gh', '''
if [ -n "${FAKE_RELEASE_FAILURE:-}" ]; then echo "$FAKE_RELEASE_FAILURE" >&2; exit 77; fi
case "$1 $2" in
  "release list") printf '[{"tagName":"%s","createdAt":"2026-10-10T12:00:00Z","isDraft":false}]\\n' "$FAKE_RELEASE_TAG" ;;
  api\\ repos/the-omega-institute/trureturing/releases/tags/*)
    printf '{"draft":false,"tag_name":"%s","assets":[{"name":"manifest.json","digest":"sha256:%s"},{"name":"lean-build.tgz","digest":"sha256:%s","size":1}]}\\n' "$FAKE_RELEASE_TAG" "$FAKE_RELEASE_MANIFEST_DIGEST" "$(printf a%.0s {1..64})" ;;
  "release download")
    while [ "$#" -gt 0 ]; do
      if [ "$1" = --dir ]; then dir="$2"; fi
      shift
    done
    cp "$FAKE_RELEASE_MANIFEST" "$dir/manifest.json" ;;
  *) echo "unsupported gh invocation: $*" >&2; exit 78 ;;
esac
''')
        self.environment['PATH'] = str(self.root / 'bin') + os.pathsep + self.environment['PATH']
        return tag

    def stale_release_fixture(self, *, local_base=None, producer=None, failure=None, fetch_failure=None):
        subprocess.run(['git', '-C', str(self.root), 'branch', '-M', 'dev'], check=True, capture_output=True)
        initial = subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        local_base = local_base or initial
        if producer is None:
            producer = self.git_commit('published release', empty=True)
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        self.write_base(local_base)
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(self.output)
        self.release_stub(producer, failure=failure)
        if fetch_failure is not None:
            self.environment['FAKE_FETCH_FAILURE'] = str(fetch_failure)
        self.script('tools/scripts/worktree/lean-cache-publish.sh',
                    'if [ -n "${FAKE_FETCH_FAILURE:-}" ]; then exit "$FAKE_FETCH_FAILURE"; fi\n'
                    'printf "fetch %s\\n" "$*" >> calls\n'
                    'mkdir -p .lake/build/stratalint\n'
                    'cp dev-seed/* .lake/build/stratalint/\n'
                    'python3 -B - "$@" <<\'PY\'\n'
                    'import json, sys\n'
                    'args = sys.argv[1:]\n'
                    'print("LEAN_CACHE_FETCH " + json.dumps(dict(status="unpacked", installed=["build"],\n'
                    '    resolved=args[args.index("--approved-tag") + 1],\n'
                    '    producer_commit_sha=args[args.index("--approved-producer") + 1])))\n'
                    'PY\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean',
                        'tools/scripts/worktree/lean-cache-publish.sh'], check=True)
        self.git_commit('clean current checkout', empty=True)
        return initial, producer

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

    def test_stale_seed_fetches_newer_compatible_release_then_uses_incremental_path(self):
        initial, release = self.stale_release_fixture()
        result = self.run_entry()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.calls[0].split()[0], 'fetch', '[FAIL] newer_release_fetches_before_incremental_build')
        self.assertIn('ensure', self.calls)
        self.assertTrue(any(call.startswith('lake ') for call in self.calls))
        self.assertIn('"action":"fetch"', result.stdout)
        self.assertIn(release, result.stdout)
        self.assertNotEqual(initial, release)

    def test_stale_seed_keeps_local_when_release_is_older_than_local_base(self):
        subprocess.run(['git', '-C', str(self.root), 'branch', '-M', 'dev'], check=True, capture_output=True)
        older = subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        newer = self.git_commit('local newer base', empty=True)
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        self.write_base(newer)
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(self.output)
        self.release_stub(older)
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean'], check=True)
        self.git_commit('clean changed inputs', empty=True)
        result = self.run_entry()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.calls[0], 'ensure', '[FAIL] older_release_keeps_local_seed')
        self.assertNotIn('fetch ', '\n'.join(self.calls))
        self.assertIn('"reason":"release-not-newer"', result.stdout)

    def test_stale_seed_keeps_local_when_release_is_not_head_ancestor(self):
        self.stale_release_fixture(producer='f' * 40)
        result = self.run_entry()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.calls[0], 'ensure', '[FAIL] foreign_release_keeps_local_seed')
        self.assertNotIn('fetch ', '\n'.join(self.calls))
        self.assertIn('"reason":"release-head-ancestry-unprovable"', result.stdout)

    def test_stale_seed_with_unknown_base_keeps_local_conservatively(self):
        _, release = self.stale_release_fixture()
        (self.root / '.lake/lean-report-seed-base.json').unlink()
        result = self.run_entry()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.calls[0], 'ensure', '[FAIL] unknown_base_keeps_local_seed')
        self.assertNotIn('fetch ', '\n'.join(self.calls))
        self.assertIn('"action":"keep"', result.stdout)
        self.assertIn('"reason":"local-base-unknown"', result.stdout)
        self.assertNotIn(release, result.stdout, '[FAIL] unknown_base_needs_no_release_information')

    def test_stale_seed_release_listing_failure_keeps_local_and_continues(self):
        self.stale_release_fixture(failure='listing failed')
        result = self.run_entry()
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue(self.calls, '[FAIL] listing_failure_continues_incrementally')
        self.assertEqual(self.calls[0], 'ensure')
        self.assertNotIn('fetch ', '\n'.join(self.calls))
        self.assertIn('"action":"keep"', result.stdout)
        self.assertIn('listing failed', result.stdout)

    def test_stale_seed_release_download_failure_keeps_local_and_continues(self):
        self.stale_release_fixture(fetch_failure=19)
        result = self.run_entry()
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.calls[0], 'ensure')
        self.assertNotIn('fetch ', '\n'.join(self.calls))
        self.assertIn('"action":"keep"', result.stdout)
        self.assertIn('"reason":"release-download-failed"', result.stdout)


    def test_unknown_base_never_lists_or_downloads(self):
        self.canonical_release_fixture()
        (self.root / self.api.BASE_RECORD).unlink()
        before = self.seed_bytes()
        result = self.refresh_canonical()
        self.assertIn('"reason":"local-base-unknown"', result.stdout)
        self.assertFalse((self.root / 'releases/calls.jsonl').exists(),
                         '[FAIL] unknown_base_never_contacts_releases')
        self.assertEqual(before, self.seed_bytes())

    def test_unclean_checkout_never_lists_or_downloads(self):
        self.canonical_release_fixture()
        before = self.seed_bytes()
        base = (self.root / self.api.BASE_RECORD).read_bytes()
        for path in ('D5/A.lean', 'untracked.txt', 'D5/Untracked.lean'):
            with self.subTest(path=path):
                target = self.root / path
                previous = target.read_bytes() if target.exists() else None
                target.write_text('def dirty := 3\n')
                result = self.refresh_canonical()
                self.assertIn('"reason":"unclean-checkout"', result.stdout,
                              '[FAIL] unclean_checkout_names_keep_reason')
                self.assertFalse((self.root / 'releases/calls.jsonl').exists(),
                                 '[FAIL] unclean_checkout_never_contacts_releases')
                self.assertEqual(before, self.seed_bytes())
                self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
                if previous is None:
                    target.unlink()
                else:
                    target.write_bytes(previous)

    def test_current_seed_prints_keep_receipt(self):
        self.canonical_release_fixture()
        self.fixture.bundle()
        publication.publish(self.seed, self.output, publication.coordinates(self.root), self.root)
        self.api.seal(self.root, self.output, self.api.capture(self.root), publication.bundle_identity(self.output))
        result = self.refresh_canonical()
        self.assertIn('"action":"keep"', result.stdout, '[FAIL] current_seed_prints_decision')
        self.assertIn('"reason":"seed-current"', result.stdout)
        self.assertFalse((self.root / 'releases/calls.jsonl').exists())

    def test_custom_output_production_preserves_canonical_base(self):
        self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        custom = self.root / 'custom-output' / publication.RAW
        captured = self.api.capture(self.root)
        self.fixture.bundle()
        publication.publish(self.seed, custom, publication.coordinates(self.root), self.root)
        self.api.seal(self.root, custom, captured, publication.bundle_identity(custom))
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes(),
                         '[FAIL] custom_output_preserves_canonical_base')
        self.assertEqual(before, self.seed_bytes())
        self.assertTrue(self.api.seed_format(custom)['compatible'])

    def test_custom_output_capture_preserves_canonical_base(self):
        self.canonical_release_fixture()
        base = (self.root / self.api.BASE_RECORD).read_bytes()
        result = subprocess.run([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
            'capture', '--repository', str(self.root), '--report', str(self.root / 'custom-output' / publication.RAW),
            '--snapshot', str(self.root / '.lake/custom-inputs.json')], env=self.environment,
            capture_output=True, text=True)
        self.assertEqual(0, result.returncode, result.stderr)
        self.assertTrue((self.root / self.api.BASE_RECORD).exists(),
                        '[FAIL] custom_capture_keeps_canonical_base')
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())


    def test_restore_between_publication_and_seal_preserves_installed_base(self):
        _, producer, _ = self.canonical_release_fixture()
        captured = self.api.capture(self.root)
        self.fixture.bundle()
        produced_sha256 = publication.publish(self.seed, self.output, publication.coordinates(self.root), self.root)
        result = subprocess.run(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
            'fetch', '--repository', str(self.root), '--refresh-stale'], env=self.environment,
            capture_output=True, text=True, check=True)
        self.assertIn('"status":"unpacked"', result.stdout)
        self.assertEqual(producer, self.api.read_seed_base(self.root))
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        try:
            self.api.seal(self.root, self.output, captured, produced_sha256)
        except ValueError:
            pass
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes(),
                         '[FAIL] replaced_generation_is_not_relabelled')
        self.assertEqual(before, self.seed_bytes(), '[FAIL] replaced_generation_is_not_resealed')

    def test_untracked_recovery_install_has_unknown_base(self):
        self.canonical_release_fixture()
        self.fixture.write('D5/Untracked.lean', 'def untracked := 3\n')
        result = subprocess.run(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
            'fetch', '--repository', str(self.root), '--refresh-stale'], env=self.environment,
            capture_output=True, text=True, check=True)
        self.assertIn('"status":"unpacked"', result.stdout)
        self.assertIsNone(self.api.read_seed_base(self.root), '[FAIL] untracked_restore_has_unknown_base')
        self.assertFalse((self.root / self.api.BASE_RECORD).exists())


    def test_entry_production_binds_canonical_identity(self):
        self.canonical_release_fixture()
        identity = self.prepare_production_entry()
        result = self.run_entry('--cache-miss-policy', 'build', direct=True)
        self.assertEqual(0, result.returncode, '[FAIL] canonical_production_entry_succeeds: ' + result.stderr)
        self.assertIn('sha256=' + identity, result.stdout)
        record = json.loads((self.root / self.api.BASE_RECORD).read_text())
        self.assertEqual(self.api.seed_identity(self.output), record['seed_sha256'])
        head = subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        self.assertEqual(head, self.api.read_seed_base(self.root))
        self.assertTrue(self.api.seed_format(self.output)['compatible'])

    def test_entry_custom_production_preserves_canonical_base(self):
        self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        identity = self.prepare_production_entry()
        canonical = self.output
        self.output = self.root / 'custom-output' / publication.RAW
        result = self.run_entry('--cache-miss-policy', 'build', direct=True)
        self.assertEqual(0, result.returncode, '[FAIL] custom_production_entry_succeeds: ' + result.stderr)
        self.assertIn('sha256=' + identity, result.stdout)
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
        for path, contents in before.items():
            self.assertEqual(contents, (self.root / '.lake/build' / path).read_bytes())
        self.assertTrue(self.api.seed_format(canonical)['compatible'])
        self.assertTrue(self.api.seed_format(self.output)['compatible'])

    def test_entry_restore_before_seal_is_excluded(self):
        self.canonical_release_fixture()
        identity = self.prepare_production_entry(restore_before_seal=True)
        result = self.run_entry('--cache-miss-policy', 'build', '--log-dir', str(self.root / 'logs'), direct=True)
        self.assertEqual(0, result.returncode, '[FAIL] guarded_publication_and_seal_succeed: ' + result.stderr)
        attempt = json.loads((self.root / 'logs/restore-before-seal.json').read_text())
        self.assertNotEqual(0, attempt['exit'], '[FAIL] restore_is_excluded_before_seal')
        self.assertIn('"status":"miss"', attempt['stdout'])
        self.assertIn('sha256=' + identity, result.stdout)
        head = subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        self.assertEqual(head, self.api.read_seed_base(self.root))
        self.assertTrue(self.api.seed_format(self.output)['compatible'],
                        '[FAIL] guarded_generation_keeps_produced_receipt')

    def test_approved_archive_failure_never_falls_back_to_older_seed(self):
        local, _, tag = self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        self.environment['FAKE_ARCHIVE_FAILURE'] = tag
        result = self.refresh_canonical()
        self.assertEqual(before, self.seed_bytes(), '[FAIL] approved_failure_preserves_seed')
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes(),
                         '[FAIL] approved_failure_preserves_base')
        self.assertEqual(local, self.api.read_seed_base(self.root))
        self.assertIn('"action":"keep"', result.stdout, '[FAIL] failed_fetch_reports_keep')
        calls = [json.loads(line) for line in (self.root / 'releases/calls.jsonl').read_text().splitlines()]
        downloads = [call[2] for call in calls if call[:2] == ['release', 'download']]
        self.assertEqual({tag}, set(downloads), '[FAIL] restore_uses_only_approved_tag')

    def test_approved_restore_installs_decision_producer_instead_of_head(self):
        local, producer, tag = self.canonical_release_fixture()
        result = self.refresh_canonical()
        self.assertEqual(producer, self.api.read_seed_base(self.root), '[FAIL] restored_base_is_manifest_producer')
        self.assertEqual(producer, (self.root / '.lake/build/producer.txt').read_text(),
                         '[FAIL] installed_producer_equals_decision')
        self.assertIn('"action":"fetch"', result.stdout)
        decision = json.loads(next(line.partition(' ')[2] for line in result.stdout.splitlines()
                                   if line.startswith('LEAN_REPORT_SEED_DECISION ')))
        self.assertEqual((local, producer, tag), (decision['local'], decision['release'], decision['tag']))
        calls = [json.loads(line) for line in (self.root / 'releases/calls.jsonl').read_text().splitlines()]
        self.assertEqual(1, sum(call[:2] == ['release', 'list'] for call in calls),
                         '[FAIL] approved_fetch_does_not_reselect')


    def test_changed_manifest_producer_is_rejected_before_installation(self):
        self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        self.environment['FAKE_CHANGED_PRODUCER'] = subprocess.check_output(
            ['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        result = self.refresh_canonical()
        self.assertEqual(before, self.seed_bytes(), '[FAIL] changed_manifest_identity_preserves_seed')
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
        self.assertIn('"action":"keep"', result.stdout)

    def test_zero_exit_without_installation_reports_keep(self):
        self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        self.script('tools/scripts/worktree/lean-cache-publish.sh',
                    'printf "skipped-fetch-ran\\n" >> calls\n'
                    'printf \'LEAN_CACHE_FETCH {"status":"skipped","reason":"fixture skip"}\\n\'\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'tools/scripts/worktree/lean-cache-publish.sh'],
                       check=True, capture_output=True)
        self.git_commit('skipped installation fixture', empty=True)
        result = self.refresh_canonical()
        self.assertEqual(before, self.seed_bytes())
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
        self.assertIn('"action":"keep"', result.stdout, '[FAIL] zero_exit_is_not_installation')
        self.assertIn('"reason":"release-installation-skipped"', result.stdout,
                      '[FAIL] zero_exit_without_installation_has_skipped_reason')
        self.assertIn('skipped-fetch-ran', (self.root / 'calls').read_text().splitlines(),
                      '[FAIL] skipped_fetch_branch_is_reached')

    def test_dirty_recovery_install_invalidates_previous_base(self):
        self.canonical_release_fixture()
        self.fixture.write('D5/A.lean', 'def a := 3\n')
        result = subprocess.run(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
            'fetch', '--repository', str(self.root), '--refresh-stale'], env=self.environment,
            text=True, capture_output=True, timeout=30)
        print('CASE ' + self._testMethodName + '\n' + result.stdout, flush=True)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertFalse((self.root / self.api.BASE_RECORD).exists(), '[FAIL] dirty_restore_removes_old_base')

    def test_rejected_staged_report_preserves_canonical_seed_and_base(self):
        for damage in ('format', 'incomplete'):
            with self.subTest(damage=damage):
                if damage == 'incomplete':
                    self.doCleanups()
                    self.setUp()
                self.canonical_release_fixture(damage=damage)
                before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
                result = self.refresh_canonical()
                self.assertEqual(before, self.seed_bytes(), '[FAIL] staged_rejection_preserves_seed')
                self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes(),
                                 '[FAIL] staged_rejection_preserves_base')
                self.assertIn('"action":"keep"', result.stdout)

    def test_equal_release_producer_does_not_fetch(self):
        _, producer, _ = self.canonical_release_fixture()
        self.write_base(producer)
        before = self.seed_bytes()
        result = self.refresh_canonical()
        self.assertEqual(before, self.seed_bytes(), '[FAIL] equal_producer_preserves_seed')
        self.assertIn('"reason":"release-not-newer"', result.stdout, '[FAIL] equality_is_not_newer')
        calls = [json.loads(line) for line in (self.root / 'releases/calls.jsonl').read_text().splitlines()]
        self.assertFalse(any('lean-build.tgz' in call for call in calls), '[FAIL] equal_producer_never_downloads_archive')

    def inject_restore_error(self, operation):
        site = self.root / '.lake/injection'
        site.mkdir(exist_ok=True)
        (site / 'sitecustomize.py').write_text('''import os, pathlib, shutil
replace, rmtree = os.replace, shutil.rmtree
def failed_replace(source, target):
    if pathlib.Path(target).name == 'lean-report-seed-base.json':
        raise OSError('injected base write failure')
    return replace(source, target)
def failed_cleanup(path, *args, **kwargs):
    name = pathlib.Path(path).name
    if name.startswith(os.environ.get('FAKE_CLEANUP_PREFIX', 'no-match')):
        raise OSError('injected cleanup failure')
    return rmtree(path, *args, **kwargs)
if os.environ.get('FAKE_BASE_WRITE_FAILURE') == '1':
    os.replace = failed_replace
shutil.rmtree = failed_cleanup
''')
        self.environment['PYTHONPATH'] = str(site)
        if operation == 'base':
            self.environment['FAKE_BASE_WRITE_FAILURE'] = '1'
        else:
            self.environment['FAKE_CLEANUP_PREFIX'] = operation

    def test_optional_base_write_failure_rolls_back_seed_and_base(self):
        self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        self.inject_restore_error('base')
        result = self.refresh_canonical()
        self.assertEqual(before, self.seed_bytes(), '[FAIL] late_base_failure_rolls_back_seed')
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes(),
                         '[FAIL] late_base_failure_rolls_back_base')
        self.assertIn('"action":"keep"', result.stdout)
        self.assertIn('approved snapshot base could not be recorded', result.stdout)

    def test_staging_cleanup_failure_rolls_back_seed_and_base(self):
        self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        self.inject_restore_error('.release-')
        result = self.refresh_canonical()
        self.assertEqual(before, self.seed_bytes(), '[FAIL] staging_cleanup_failure_rolls_back_seed')
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
        self.assertIn('"action":"keep"', result.stdout)
        self.assertIn('injected cleanup failure', result.stdout)

    def test_backup_cleanup_failure_reports_committed_installation(self):
        _, producer, _ = self.canonical_release_fixture()
        self.inject_restore_error('.release-backup-')
        result = self.refresh_canonical()
        self.assertEqual(producer, self.api.read_seed_base(self.root), '[FAIL] committed_cleanup_failure_has_new_base')
        self.assertEqual(producer, (self.root / '.lake/build/producer.txt').read_text())
        self.assertIn('"action":"fetch"', result.stdout, '[FAIL] committed_cleanup_failure_reports_fetch')

    def test_skipped_restore_does_not_write_snapshot_base(self):
        local, _, tag = self.canonical_release_fixture()
        build, private = self.root / '.lake/build', self.root / 'private-build'
        build.rename(private)
        build.symlink_to(private, target_is_directory=True)
        before = (self.root / self.api.BASE_RECORD).read_bytes()
        result = subprocess.run(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
            'fetch', '--repository', str(self.root), '--refresh-stale'], env=self.environment,
            text=True, capture_output=True, timeout=30)
        self.assertEqual(0, result.returncode, result.stdout + result.stderr)
        self.assertEqual(before, (self.root / self.api.BASE_RECORD).read_bytes(), '[FAIL] skipped_install_keeps_base')
        self.assertEqual(local, self.api.read_seed_base(self.root))
        self.assertIn('"status":"skipped"', result.stdout)

    def test_production_capture_invalidates_base_before_report_build(self):
        self.canonical_release_fixture()
        self.fixture.write('D5/A.lean', 'def a := 3\n')
        result = self.run_entry('REBUILD_REPORT_CACHE=1')
        self.assertNotEqual(0, result.returncode)
        self.assertTrue(any(call.startswith('lake ') for call in self.calls))
        self.assertFalse((self.root / self.api.BASE_RECORD).exists(), '[FAIL] production_clears_base_before_new_seed')

    def test_optional_refresh_in_ci_or_non_dev_or_detached_keeps_seed(self):
        self.canonical_release_fixture()
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        for scope in ('ci', 'non-dev', 'detached'):
            with self.subTest(scope=scope):
                self.environment['GITHUB_ACTIONS'] = 'true' if scope == 'ci' else 'false'
                if scope == 'non-dev':
                    subprocess.run(['git', '-C', str(self.root), 'branch', '-M', 'topic'], check=True)
                elif scope == 'detached':
                    subprocess.run(['git', '-C', str(self.root), 'checkout', '-q', '--detach'], check=True)
                result = self.refresh_canonical()
                self.assertEqual(before, self.seed_bytes(), '[FAIL] excluded_scope_preserves_seed')
                self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
                self.assertIn('"action":"keep"', result.stdout)
                self.assertFalse((self.root / 'releases/calls.jsonl').exists(), '[FAIL] excluded_scope_never_lists')

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
