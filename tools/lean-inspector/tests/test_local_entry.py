"""Local report recovery uses real receipts with stubbed transport and Lake."""
import json
import os
import shutil
import subprocess
import sys
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
        for name in ('reuse.py', 'publication.py', 'materials.py'):
            self.copy('tools/lean-inspector/' + name)
        self.copy('tools/scripts/report/lean-report.sh')
        self.copy('Makefile')
        self.fixture.write('tools/lean-inspector/inspect.sh', '''#!/bin/bash
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
exec python3 -B "$root/inspector_stub.py" "$@"
''')
        self.fixture.write('inspector_stub.py', '''import os, pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(root / 'tools/lean-inspector'))
import reuse
(root / 'inspect-called').write_text(' '.join(sys.argv[1:]))
seed = pathlib.Path(os.environ.get('STRATALINT_LEAN_REPORT_SEED', str(root / '.lake/build/stratalint/raw-lean-report.json')))
if os.environ.get('STRATALINT_LEAN_REPORT_REUSE') == '0' or reuse.probe(root, seed)['needs_lake']:
    subprocess.run([os.environ['LAKE_BIN']], check=True)
print('INSPECTOR_CONTINUED')
''')
        self.fixture.write('bin/lake', '#!/bin/bash\nprintf called > "$(dirname "$0")/../lake-called"\n')
        self.fixture.write('tools/scripts/worktree/lean-cache-publish.sh', '''#!/bin/bash
set -euo pipefail
root="$(cd "$(dirname "$0")/../../.." && pwd)"
printf '%s\\n' "$*" >> "$root/fetch-called"
[[ "$*" == 'fetch --mode production --refresh-stale' ]] || exit 92
[[ "${FETCH_RESULT:-ok}" != unavailable ]] || exit 9
mkdir -p "$root/.lake/build/stratalint"
cp "$root"/dev-seed/* "$root/.lake/build/stratalint/"
''')
        for name in ('tools/lean-inspector/inspect.sh', 'bin/lake',
                     'tools/scripts/worktree/lean-cache-publish.sh'):
            (self.root / name).chmod(0o755)
        self.environment = dict(os.environ, LAKE_BIN=str(self.root / 'bin/lake'),
                                STRATALINT_LEAN_REPORT_REUSE='1')
        for name in ('LEAN_REPORT', 'STRATALINT_LEAN_REPORT_SEED', 'REBUILD_REPORT_CACHE',
                     'LEAN_CACHE_MODE', 'LEAN_CACHE_SOURCE_REF', 'LEAN_CACHE_SOURCE_COMMIT'):
            self.environment.pop(name, None)
        self.dev_seed(1)

    def copy(self, name):
        target = self.root / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(fixtures.ROOT / name, target)

    def dev_seed(self, version):
        target = self.root / 'dev-seed'
        target.mkdir(exist_ok=True)
        for source in self.seed.parent.iterdir():
            if source.is_file():
                shutil.copyfile(source, target / source.name)
        receipt = target / (self.seed.name + '.reuse.json')
        record = json.loads(receipt.read_text())
        record['inputs']['semantic_version'] = version
        receipt.write_text(json.dumps(record))

    def current_version(self, version):
        self.fixture.policy['report_cache_release_semantic_version'] = version
        self.fixture.write_policy()

    def entry(self, *arguments):
        return subprocess.run(['make', '--no-print-directory', 'lean-report', *arguments],
                              cwd=self.root, env=self.environment, text=True, capture_output=True)

    def assert_continued(self, result, fetched=True, lake=False):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('INSPECTOR_CONTINUED', result.stdout)
        self.assertEqual((self.root / 'fetch-called').exists(), fetched)
        if fetched:
            self.assertEqual((self.root / 'fetch-called').read_text().splitlines(),
                             ['fetch --mode production --refresh-stale'])
        self.assertEqual((self.root / 'lake-called').exists(), lake)

    def assert_blocked(self, result, local, current, dev, reason):
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse((self.root / 'inspect-called').exists())
        self.assertFalse((self.root / 'lake-called').exists(), 'Lake must not run on incompatible seeds')
        self.assertIn(f'LEAN_REPORT_CACHE_INCOMPATIBLE local_version={local} current_version={current} '
                      f'dev_seed_version={dev} reason={reason}', result.stderr)
        self.assertIn('make lean-report REBUILD_REPORT_CACHE=1', result.stderr)
        self.assertEqual(len((self.root / 'fetch-called').read_text().splitlines()), 1)

    def test_missing_seed_recovers_before_inspection(self):
        shutil.rmtree(self.seed.parent)
        self.assert_continued(self.entry())

    def test_version_mismatch_recovers_before_inspection(self):
        self.current_version(2)
        self.dev_seed(2)
        self.assert_continued(self.entry())

    def test_dev_seed_still_incompatible_never_calls_lake(self):
        self.current_version(2)
        self.assert_blocked(self.entry(), 1, 2, 1, 'version-mismatch')

    def test_fetch_unavailable_never_calls_lake(self):
        self.current_version(2)
        self.environment['FETCH_RESULT'] = 'unavailable'
        self.assert_blocked(self.entry(), 1, 2, 'unavailable', 'fetch-unavailable')

    def test_fetch_success_without_seed_never_calls_lake(self):
        shutil.rmtree(self.seed.parent)
        self.fixture.write('tools/scripts/worktree/lean-cache-publish.sh',
                           '#!/bin/bash\nprintf called > "$(dirname "$0")/../../../fetch-called"\n')
        self.assert_blocked(self.entry(), 'unavailable', 1, 'unavailable', 'seed-unavailable')

    def test_explicit_rebuild_skips_check_and_uses_full_path(self):
        self.current_version(2)
        path = self.root / 'tools/lean-inspector/reuse.py'
        path.write_text(path.read_text().replace("if __name__ == '__main__':",
                                                "if __name__ == '__main__':\n    raise SystemExit(91)"))
        self.assert_continued(self.entry('REBUILD_REPORT_CACHE=1'), fetched=False, lake=True)

    def test_explicit_rebuild_forces_full_path_even_with_matching_seed(self):
        self.assert_continued(self.entry('REBUILD_REPORT_CACHE=1'), fetched=False, lake=True)

    def test_same_version_input_change_uses_existing_path_without_fetch(self):
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        self.assert_continued(self.entry(), fetched=False, lake=True)

    def test_matching_seed_has_no_fetch_or_lake(self):
        self.assert_continued(self.entry(), fetched=False)

    def test_local_entry_does_not_depend_on_ci_environment(self):
        self.current_version(2)
        self.environment['GITHUB_ACTIONS'] = 'true'
        self.assert_blocked(self.entry(), 1, 2, 1, 'version-mismatch')

    def test_seed_version_check_is_read_only_and_does_not_capture_inputs(self):
        import reuse
        before = {path: (path.read_bytes(), path.stat().st_mtime_ns)
                  for path in self.seed.parent.iterdir()}
        with patch.object(reuse, 'capture', side_effect=AssertionError('must not capture inputs')), \
                patch.object(reuse.publication, 'digest', side_effect=AssertionError('must not hash files')):
            status = reuse.seed_version(self.root, self.seed)
        self.assertEqual(status, dict(local_version=1, current_version=1, reason='version-matched'))
        self.assertEqual(before, {path: (path.read_bytes(), path.stat().st_mtime_ns)
                                  for path in self.seed.parent.iterdir()})

    def test_custom_output_uses_fetched_default_seed(self):
        self.environment['LEAN_REPORT'] = 'custom/report.json'
        self.assert_continued(self.entry())
        self.assertIn('--output custom/report.json', (self.root / 'inspect-called').read_text())

    def test_refresh_stale_make_option_reaches_fetch(self):
        self.fixture.write('tools/scripts/worktree/lean-cache-publish.sh', '#!/bin/bash\nprintf "%s\\n" "$*"\n')
        result = subprocess.run(['make', '--no-print-directory', 'lean-cache-from-github-without-mathlib',
                                 'REFRESH_STALE=1'], cwd=self.root, env=self.environment,
                                text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('--refresh-stale', result.stdout)

    def test_release_publisher_bypasses_local_guard_and_preserves_build_failure(self):
        sys.path.insert(0, str(fixtures.ROOT / 'tools/scripts/worktree'))
        import lean_cache_release
        with patch.object(lean_cache_release.subprocess, 'run', return_value=subprocess.CompletedProcess([], 41)) as run, \
                patch.dict(os.environ, STRATALINT_LEAN_REPORT_LOG_DIR='publisher logs'):
            self.assertEqual(lean_cache_release.publish(self.root, 'fixture/partition'), 41)
        run.assert_called_once_with(['/bin/bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
                                     '--repository', str(self.root), '--output',
                                     '.lake/build/stratalint/raw-lean-report.json',
                                     '--log-dir', 'publisher logs'], cwd=self.root)
