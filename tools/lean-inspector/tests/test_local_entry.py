"""Real local report entry with external download and native execution fixtures."""
import json
import os
from pathlib import Path
import select
import shutil
import subprocess
import sys
import time
import unittest
from unittest.mock import patch

import test_reuse as fixtures


class LocalReportEntryTests(unittest.TestCase):
    def setUp(self):
        self.fixture = fixtures.ReuseTests()
        self.fixture.setUp()
        self.addCleanup(self.fixture.doCleanups)
        self.root = self.fixture.root
        self.seed = self.root / '.lake/build/stratalint/raw-lean-report.json'
        self.fixture.report = self.seed
        self.seed.parent.mkdir(parents=True)
        self.fixture.receipt()
        for name in ('reuse.py', 'publication.py', 'materials.py', 'inspect.sh'):
            self.copy('tools/lean-inspector/' + name)
        for name in ('lean-report.sh', 'report-supervisor.sh', 'report_supervisor.py'):
            if (fixtures.ROOT / 'tools/scripts/report' / name).exists():
                self.copy('tools/scripts/report/' + name)
        self.copy('tools/scripts/lib/resource-observation-lib.sh')
        for name in ('lean_cache_release.py', 'lean_cache.py', 'cache_material.py'):
            self.copy('tools/scripts/worktree/' + name)
        self.copy('Makefile')
        self.fixture.write('producer.dll', 'native execution fixture')
        # The native runner records report-facet entry and returns a sentinel.
        # Publication/sealing are intentionally unreachable after that failure;
        # selected program builds remain successful and are recorded separately.
        self.executable('tools/scripts/worktree/lean-cache-run.sh',
                        'if [[ "$*" == *" :report"* ]]; then\n'
                        '  printf "%s\\n" "$*" >> report-builds\n'
                        '  exit 73\n'
                        'fi\n'
                        'printf "%s\\n" "$*" >> program-builds\n')
        self.executable('tools/scripts/worktree/lean-cache-ensure.sh', 'exit 0\n')
        self.executable('tools/scripts/worktree/lean-cache-publish.sh',
                        'exec python3 -B "$(dirname "$0")/fetch_fixture.py" "$@"\n')
        self.fixture.write('tools/scripts/worktree/fetch_fixture.py', '''import contextlib, os, pathlib, shutil, sys
from lean_cache_release import cache_guard
root = pathlib.Path(__file__).resolve().parents[3]
args = sys.argv[1:]
with (root / "fetch-called").open("a") as log:
    log.write(" ".join(args) + "\\n")
assert args[:2] == ["fetch", "--mode"] and "production" in args and "--refresh-stale" in args, args
with (root / "fetch-seeded-marker").open("w") as marker:
    marker.write(os.environ.get("STRATALINT_ACTIONS_CACHE_SEEDED", ""))
if os.environ.get("STRATALINT_ACTIONS_CACHE_SEEDED", "").lower() in ("1", "true"):
    (root / "fetch-skipped-by-seeded-marker").write_text("1")
    raise SystemExit(0)
if os.environ.get("FETCH_RESULT") == "unavailable":
    raise SystemExit(9)
with contextlib.nullcontext() if "--writer-owned" in args else cache_guard(root):
    destination = root / ".lake/build/stratalint"
    destination.mkdir(parents=True, exist_ok=True)
    for source in (root / "dev-seed").iterdir():
        shutil.copyfile(source, destination / source.name)
''')
        self.executable('bin/lake', 'if [[ "$1" == --version ]]; then\n'
                        '  printf "%s\\n" "fixture lake 1"\n'
                        'else\n'
                        '  printf "%s\\n" "$*" >> lake-calls\n'
                        'fi\n')
        self.environment = dict(os.environ, LAKE_BIN=str(self.root / 'bin/lake'),
                                STRATALINT_INSPECTOR_SUPERVISED='1',
                                STRATALINT_LEAN_BUILD_TARGETS='[]',
                                STRATALINT_LEAN_PRODUCER_DLL=str(self.root / 'producer.dll'))
        for name in ('LEAN_REPORT', 'STRATALINT_LEAN_REPORT_SEED', 'STRATALINT_LEAN_REPORT_REUSE',
                     'REBUILD_REPORT_CACHE', 'LEAN_REPORT_CACHE_MISS_POLICY', 'FETCH_RESULT'):
            self.environment.pop(name, None)
        self.dev_seed(1)

    def copy(self, name):
        target = self.root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(fixtures.ROOT / name, target)

    def executable(self, name, body):
        self.fixture.write(name, '#!/bin/bash\nset -euo pipefail\n' + body)
        (self.root / name).chmod(0o755)

    def dev_seed(self, version):
        target = self.root / 'dev-seed'
        target.mkdir(exist_ok=True)
        previous = self.fixture.policy['report_cache_release_semantic_version']
        self.fixture.policy['report_cache_release_semantic_version'] = version
        self.fixture.write_policy()
        self.fixture.report = target / self.seed.name
        self.fixture.receipt()
        self.fixture.report = self.seed
        self.fixture.policy['report_cache_release_semantic_version'] = previous
        self.fixture.write_policy()

    def set_version(self, path, version):
        record = json.loads(path.read_text())
        record['inputs']['semantic_version'] = version
        path.write_text(json.dumps(record))

    def current_version(self, version):
        self.fixture.policy['report_cache_release_semantic_version'] = version
        self.fixture.write_policy()

    def alternate_seed(self, version):
        alternate = self.root / 'alternate seed' / self.seed.name
        alternate.parent.mkdir(exist_ok=True)
        for source in self.seed.parent.iterdir():
            if source.is_file():
                shutil.copyfile(source, alternate.parent / source.name)
        self.set_version(Path(str(alternate) + '.reuse.json'), version)
        return alternate

    def entry(self, *arguments, environment=None, cwd=None):
        return subprocess.run(['make', '--no-print-directory', '-C', str(self.root), 'lean-report', *arguments],
                              cwd=cwd or self.root, env=environment or self.environment,
                              text=True, capture_output=True, timeout=30)

    def make_target(self, target, *arguments):
        return subprocess.run(['make', '--no-print-directory', target, *arguments],
                              cwd=self.root, env=self.environment,
                              text=True, capture_output=True, timeout=30)

    def assert_continued(self, result, fetched=True, output=None):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('complete-entry-reused', result.stdout)
        self.assertEqual((self.root / 'fetch-called').exists(), fetched)
        if fetched:
            self.assertEqual((self.root / 'fetch-called').read_text().splitlines(),
                             ['fetch --mode production --refresh-stale --writer-owned'])
        self.assertFalse((self.root / 'report-builds').exists())
        self.assertTrue(Path(str(output or self.seed) + '.reuse.json').is_file())

    def assert_build(self, result):
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn('build :report', (self.root / 'report-builds').read_text())
        self.assertFalse((self.root / 'fetch-called').exists())
        self.assertNotIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stderr)

    def assert_blocked(self, result, local, current, dev, reason, fetched=True):
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertFalse((self.root / 'report-builds').exists(), 'incompatible seeds must not enter :report')
        self.assertIn(f'LEAN_REPORT_CACHE_INCOMPATIBLE local_version={local} current_version={current} '
                      f'dev_seed_version={dev} reason={reason}', result.stderr)
        self.assertIn('make lean-report REBUILD_REPORT_CACHE=1', result.stderr)
        self.assertEqual((self.root / 'fetch-called').exists(), fetched)
        if fetched:
            self.assertEqual(len((self.root / 'fetch-called').read_text().splitlines()), 1)

    def test_missing_seed_recovers_before_consumption(self):
        shutil.rmtree(self.seed.parent)
        self.assert_continued(self.entry())

    def test_version_mismatch_recovers_before_consumption(self):
        self.current_version(2)
        self.dev_seed(2)
        self.assert_continued(self.entry())

    def test_recovery_clears_inherited_actions_seed_marker(self):
        self.current_version(2)
        self.dev_seed(2)
        self.environment['STRATALINT_ACTIONS_CACHE_SEEDED'] = '1'
        self.assert_continued(self.entry())
        self.assertEqual((self.root / 'fetch-seeded-marker').read_text(), '0')
        self.assertFalse((self.root / 'fetch-skipped-by-seeded-marker').exists())

    def test_dev_seed_still_incompatible_never_builds(self):
        self.current_version(2)
        self.assert_blocked(self.entry(), 1, 2, 1, 'version-mismatch')

    def test_fetch_unavailable_never_builds(self):
        self.current_version(2)
        self.environment['FETCH_RESULT'] = 'unavailable'
        self.assert_blocked(self.entry(), 1, 2, 'unavailable', 'fetch-unavailable')

    def test_fetch_success_without_seed_never_builds(self):
        shutil.rmtree(self.seed.parent)
        shutil.rmtree(self.root / 'dev-seed')
        (self.root / 'dev-seed').mkdir()
        self.assert_blocked(self.entry(), 'unavailable', 1, 'unavailable', 'seed-unavailable')

    def test_explicit_rebuild_skips_guard_even_with_matching_path_named_zero(self):
        zero = self.root / '0'
        self.fixture.report = zero
        self.fixture.receipt()
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(zero)
        self.assert_build(self.entry('REBUILD_REPORT_CACHE=1'))

    def test_explicit_rebuild_skips_guard_on_mismatch(self):
        self.current_version(2)
        self.assert_build(self.entry('REBUILD_REPORT_CACHE=1'))

    def test_inherited_policy_cannot_bypass_local_guard_at_any_make_entry(self):
        shutil.rmtree(self.seed.parent)
        self.environment['FETCH_RESULT'] = 'unavailable'
        for policy in ('build', 'reuse-or-build', 'invalid'):
            for target in ('lean-report', 'test', 'gate'):
                with self.subTest(policy=policy, target=target):
                    (self.root / 'fetch-called').unlink(missing_ok=True)
                    self.environment['LEAN_REPORT_CACHE_MISS_POLICY'] = policy
                    self.assert_blocked(self.make_target(target), 'unavailable', 1,
                                        'unavailable', 'fetch-unavailable')

    def test_inherited_rebuild_cannot_bypass_local_guard(self):
        shutil.rmtree(self.seed.parent)
        self.environment['FETCH_RESULT'] = 'unavailable'
        self.environment['REBUILD_REPORT_CACHE'] = '1'
        self.assert_blocked(self.entry(), 'unavailable', 1, 'unavailable', 'fetch-unavailable')

    def test_explicit_reuse_policy_reaches_nested_make(self):
        shutil.rmtree(self.seed.parent)
        for target in ('test', 'gate'):
            with self.subTest(target=target):
                self.assert_build(self.make_target(target, 'LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'))

    def test_explicit_rebuild_reaches_nested_make_test(self):
        self.assert_build(self.make_target('test', 'REBUILD_REPORT_CACHE=1'))

    def test_explicit_build_policy_requires_rebuild_option(self):
        result = self.entry('LEAN_REPORT_CACHE_MISS_POLICY=build')
        self.assertEqual(result.returncode, 2, result.stdout + result.stderr)
        self.assertIn('REBUILD_REPORT_CACHE=1', result.stderr)
        self.assertFalse((self.root / 'report-builds').exists())

    def test_same_version_input_change_keeps_incremental_path(self):
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        self.assert_build(self.entry())

    def test_matching_seed_has_no_fetch_or_report_build(self):
        self.assert_continued(self.entry(), fetched=False)

    def test_ci_reuse_or_build_matching_seed_skips_report_facet(self):
        self.environment['STRATALINT_LEAN_BUILD_TARGETS'] = '["D5/A"]'
        self.assert_continued(self.entry('LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'), fetched=False)
        program_builds = (self.root / 'program-builds').read_text().splitlines()
        self.assertEqual(len(program_builds), 1)
        self.assertTrue(program_builds[0].endswith('tools/lean-inspector-reg build D5/A'))

    def test_ci_aged_complete_actions_seed_survives_writer_owned_refresh(self):
        original = (self.root / 'D5/A.lean').read_text()
        self.fixture.write('D5/A.lean', original + 'def dev_addition := 2\n')
        self.dev_seed(1)
        self.fixture.write('D5/A.lean', original)
        aged = time.time() - 7 * 60 * 60
        for member in self.seed.parent.iterdir():
            os.utime(member, (aged, aged))
        self.environment['STRATALINT_ACTIONS_CACHE_SEEDED'] = '1'
        self.environment['STRATALINT_LEAN_BUILD_TARGETS'] = '["D5/A"]'
        self.executable('tools/scripts/worktree/lean-cache-ensure.sh',
                        'exec python3 -B "$(dirname "$0")/aged_ensure_fixture.py"\n')
        self.fixture.write('tools/scripts/worktree/aged_ensure_fixture.py', '''import shutil
from pathlib import Path
import lean_cache_release as api
root = Path(__file__).resolve().parents[3]
def transport(root, partition, deadline, refresh_stale=False):
    assert refresh_stale
    (root / 'refresh-transport-called').write_text('1')
    for source in (root / 'dev-seed').iterdir():
        shutil.copyfile(source, root / '.lake/build/stratalint' / source.name)
    return 0
api.fetch_locked = transport
# EnsureLocked's expired-cache branch holds the writer guard and requests refresh.
with api.cache_guard(root):
    raise SystemExit(api.fetch(root, 'fixture-partition', writer_owned=True, refresh_stale=True))
''')
        self.assert_continued(self.entry('LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'), fetched=False)
        self.assertFalse((self.root / 'refresh-transport-called').exists())
        self.assertIn('build D5/A', (self.root / 'program-builds').read_text())

    def test_ci_reuse_or_build_input_miss_enters_report_facet(self):
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        self.assert_build(self.entry('LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'))

    def test_ci_reuse_or_build_version_miss_enters_report_facet(self):
        self.current_version(2)
        self.assert_build(self.entry('LEAN_REPORT_CACHE_MISS_POLICY=reuse-or-build'))

    def test_default_matches_but_actual_reuse_seed_is_incompatible(self):
        self.current_version(2)
        self.dev_seed(2)
        self.set_version(Path(str(self.seed) + '.reuse.json'), 2)
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(self.alternate_seed(1))
        self.environment['FETCH_RESULT'] = 'unavailable'
        self.assert_blocked(self.entry(), 1, 2, 'unavailable', 'fetch-unavailable')

    def test_matching_alternate_seed_with_missing_default_output(self):
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(self.alternate_seed(1))
        shutil.rmtree(self.seed.parent)
        self.assert_continued(self.entry(), fetched=False)

    def test_seed_variable_cannot_bypass_actual_incompatible_seed(self):
        self.environment['STRATALINT_LEAN_REPORT_SEED'] = str(self.alternate_seed(2))
        self.current_version(2)
        self.assert_blocked(self.entry(), 1, 2, 1, 'version-mismatch')

    def test_custom_output_consumes_fetched_default_seed(self):
        self.environment['LEAN_REPORT'] = 'custom output/report.json'
        self.assert_continued(self.entry(), output=self.root / self.environment['LEAN_REPORT'])

    def test_relative_reuse_path_resolves_against_repository(self):
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(self.alternate_seed(1).relative_to(self.root))
        shutil.rmtree(self.seed.parent)
        self.assert_continued(self.entry(cwd=self.root.parent), fetched=False)

    def test_policy_does_not_depend_on_ci_environment(self):
        self.current_version(2)
        self.environment['GITHUB_ACTIONS'] = 'true'
        self.assert_blocked(self.entry(), 1, 2, 1, 'version-mismatch')

    def test_direct_inspector_default_keeps_cold_build_behavior(self):
        shutil.rmtree(self.seed.parent)
        result = subprocess.run(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
                                 '--repository', str(self.root), '--output', str(self.seed)],
                                env=self.environment, capture_output=True, text=True, timeout=30)
        self.assert_build(subprocess.CompletedProcess(result.args, 2, result.stdout, result.stderr))
        self.assertEqual(result.returncode, 73)

    def test_supervised_handoff_preserves_local_policy(self):
        self.current_version(2)
        self.environment.pop('STRATALINT_INSPECTOR_SUPERVISED')
        self.environment['STRATALINT_SUPERVISOR_ROOT'] = str(self.root / 'supervisor state')
        self.assert_blocked(self.entry(), 1, 2, 1, 'version-mismatch')

    def test_seed_version_is_read_only(self):
        import reuse
        before = {path: (path.read_bytes(), path.stat().st_mtime_ns) for path in self.seed.parent.iterdir()}
        with patch.object(reuse, 'capture', side_effect=AssertionError('must not capture inputs')), \
                patch.object(reuse.publication, 'digest', side_effect=AssertionError('must not hash files')):
            self.assertEqual(reuse.seed_version(self.root, self.seed),
                             dict(local_version=1, current_version=1, reason='version-matched'))
        self.assertEqual(before, {path: (path.read_bytes(), path.stat().st_mtime_ns)
                                  for path in self.seed.parent.iterdir()})

    def test_refresh_stale_make_option_reaches_fetch(self):
        self.executable('tools/scripts/worktree/lean-cache-publish.sh', 'printf "%s\\n" "$*"\n')
        result = subprocess.run(['make', '--no-print-directory', 'lean-cache-from-github-without-mathlib',
                                 'REFRESH_STALE=1'], cwd=self.root, env=self.environment,
                                text=True, capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('--refresh-stale', result.stdout)

    def test_concurrent_refresh_cannot_replace_checked_seed_before_consumption(self):
        self.current_version(2)
        self.fixture.receipt()
        ready, release = self.root / 'ready.fifo', self.root / 'release.fifo'
        os.mkfifo(ready)
        os.mkfifo(release)
        ready_fd = os.open(ready, os.O_RDWR | os.O_NONBLOCK)
        release_fd = os.open(release, os.O_RDWR | os.O_NONBLOCK)
        self.addCleanup(os.close, ready_fd)
        self.addCleanup(os.close, release_fd)
        # Instrument the publication boundary without replacing its behavior.
        # The real reader/publisher still consumes and validates the bundle.
        self.fixture.write('bin/sitecustomize.py', """import os, sys
if os.environ.get('BARRIER_READY'):
    sys.path.insert(0, os.environ['FIXTURE_INSPECTOR_DIRECTORY'])
    import publication
    original = publication.publish
    def publish(*args, **kwargs):
        with open(os.environ['BARRIER_READY'], 'w') as ready:
            ready.write('r')
        with open(os.environ['BARRIER_RELEASE']) as release:
            release.read(1)
        return original(*args, **kwargs)
    publication.publish = publish
""")
        first_env = dict(self.environment, BARRIER_READY=str(ready), BARRIER_RELEASE=str(release),
                         PYTHONPATH=str(self.root / 'bin'),
                         FIXTURE_INSPECTOR_DIRECTORY=str(self.root / 'tools/lean-inspector'))
        with subprocess.Popen(['make', '--no-print-directory', 'lean-report'], cwd=self.root,
                              env=first_env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE) as first:
            try:
                self.assertTrue(select.select([ready_fd], [], [], 20)[0], 'native version barrier not reached')
                os.read(ready_fd, 1)
                second = self.entry('LEAN_REPORT=concurrent/report.json')
                same_output = self.entry()
                self.assertTrue(Path(str(self.seed) + '.reuse.json').is_file())
            finally:
                os.write(release_fd, b'r')
            out, err = first.communicate(timeout=20)
        self.assert_continued(subprocess.CompletedProcess(first.args, first.returncode, out, err), fetched=False)
        self.assert_blocked(second, 'unavailable', 2, 'unavailable', 'cache-busy', fetched=False)
        self.assert_blocked(same_output, 'unavailable', 2, 'unavailable', 'cache-busy', fetched=False)

    def test_same_version_miss_handoff_keeps_refreshed_receipt_for_lake_writer(self):
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        ready = self.root / 'handoff-ready'
        release = self.root / 'handoff-release'
        self.fixture.write('bin/python3', f'''#!/bin/bash
set -euo pipefail
real="${{PYTHON_REAL:?}}"
if [[ "$*" == *"reuse.py reuse"* ]]; then
  set +e
  "$real" "$@"
  rc=$?
  set -e
  if [[ "$rc" == 3 && -n "${{HANDOFF_READY:-}}" ]]; then
    : > "$HANDOFF_READY"
    while [[ ! -f "${{HANDOFF_RELEASE:?}}" ]]; do sleep 0.01; done
  fi
  exit "$rc"
fi
exec "$real" "$@"
''')
        (self.root / 'bin/python3').chmod(0o755)
        self.executable('tools/scripts/worktree/lean-cache-run.sh', '''if [[ "$*" == *":report"* ]]; then
  if [[ -f .lake/build/stratalint/raw-lean-report.json.reuse.json ]]; then
    printf '%s\n' present > lake-entry-receipt
  else
    printf '%s\n' missing > lake-entry-receipt
  fi
fi
printf "%s\n" "$*" >> report-builds
exit 73
''')
        first_env = dict(self.environment, PATH=str(self.root / 'bin') + os.pathsep + os.environ['PATH'],
                         PYTHON_REAL=os.environ.get('PYTHON', 'python3'),
                         HANDOFF_READY=str(ready), HANDOFF_RELEASE=str(release))
        first_env['PYTHON_REAL'] = sys.executable
        with subprocess.Popen(['make', '--no-print-directory', 'lean-report'], cwd=self.root,
                              env=first_env, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE) as first:
            for _ in range(2000):
                if ready.exists():
                    break
                import time
                time.sleep(0.01)
            self.assertTrue(ready.exists(), 'reuse miss handoff barrier was not reached')
            refresh = subprocess.run(['make', '--no-print-directory', 'lean-cache-from-github-without-mathlib',
                                      'REFRESH_STALE=1'], cwd=self.root, env=self.environment,
                                     text=True, capture_output=True, timeout=30)
            self.assertEqual(refresh.returncode, 0, refresh.stdout + refresh.stderr)
            release.write_text('release\n')
            stdout, stderr = first.communicate(timeout=30)
        self.assertEqual(first.returncode, 2, stdout + stderr)
        self.assertEqual((self.root / 'lake-entry-receipt').read_text(), 'present\n')


if __name__ == '__main__':
    unittest.main()
