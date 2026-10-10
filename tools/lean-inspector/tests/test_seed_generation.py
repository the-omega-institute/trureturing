"""Complete canonical generations, selected seeds, and restore exclusion contracts."""
import hashlib
import json
import os
from pathlib import Path
import select
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import zipfile

import test_reuse
import publication

ROOT = test_reuse.ROOT


class SeedGenerationTests:
    def test_failed_entry_cleanup_preserves_competing_production(self):
        self.assert_failed_cleanup_preserves_generation('production')

    def test_failed_entry_cleanup_preserves_competing_restore(self):
        self.assert_failed_cleanup_preserves_generation('restore')

    def assert_failed_cleanup_preserves_generation(self, replacement):
        """A releases its writer guard, B commits, then A exits unsuccessfully."""
        _, release, tag = self.canonical_release_fixture()
        self.prepare_production_entry()
        current_report = self.root / 'bin/current-report.zip'
        shutil.copyfile(self.root / '.lake/build/lean-inspector/report.zip', current_report)
        self.environment['FIXTURE_CURRENT_REPORT'] = str(current_report)
        gates = self.root / '.lake/cleanup-gates'
        gates.mkdir()
        notice, resume = gates / 'notice', gates / 'resume'
        os.mkfifo(notice)
        os.mkfifo(resume)
        helper = self.root / 'bin/guarded-report.py'
        helper.write_text('''import os, shutil, sys
from pathlib import Path
sys.path.insert(0, str(Path.cwd() / 'tools/scripts/worktree'))
from lean_cache_release import cache_guard
with cache_guard(Path.cwd()):
    artifact = Path.cwd() / '.lake/build/lean-inspector/report.zip'
    artifact.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(os.environ['FIXTURE_CURRENT_REPORT'], artifact)
if os.environ.get('FIXTURE_FAIL_AFTER_GUARD') == '1':
    with open(os.environ['FIXTURE_NOTICE'], 'w') as channel:
        channel.write('guard released\\n')
    with open(os.environ['FIXTURE_RESUME']) as channel:
        channel.read()
    raise SystemExit(23)
''')
        self.script('tools/scripts/worktree/lean-cache-run.sh',
                    'exec ' + shlex.quote(sys.executable) + ' -B ' + shlex.quote(str(helper)) + '\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'tools/scripts/worktree/lean-cache-run.sh'],
                       check=True, capture_output=True)
        head = self.git_commit('guard-release fixture', empty=True)
        read_notice = os.open(notice, os.O_RDONLY | os.O_NONBLOCK)
        environment = dict(self.environment, FIXTURE_FAIL_AFTER_GUARD='1',
                           FIXTURE_NOTICE=str(notice), FIXTURE_RESUME=str(resume))
        first = subprocess.Popen(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(self.output),
            '--log-dir', str(self.root / 'logs/first'), '--cache-miss-policy', 'fetch-or-fail'],
            cwd=self.root, env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            ready, _, _ = select.select([read_notice], [], [], 30)
            self.assertTrue(ready, '[FAIL] failed_entry_reaches_released_guard_boundary')
            self.assertEqual(b'guard released\n', os.read(read_notice, 1024))
            self.assertFalse(publication.member(self.output, self.api.SUFFIX).exists(),
                             '[FAIL] preparation_already_removed_failed_receipt')
            if replacement == 'restore':
                second = subprocess.run(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
                    'fetch', '--repository', str(self.root), '--refresh-stale',
                    '--approved-tag', tag, '--approved-producer', release],
                    cwd=self.root, env=self.environment, text=True, capture_output=True, timeout=30)
                producer = release
            else:
                second = self.run_entry('--cache-miss-policy', 'fetch-or-fail',
                                        '--log-dir', str(self.root / 'logs/second'), direct=True)
                producer = head
            self.assertEqual(0, second.returncode, '[FAIL] competing_generation_completes: ' + second.stderr)
            self.assertEqual(producer, self.api.read_seed_base(self.root))
            receipt = publication.member(self.output, self.api.SUFFIX)
            before_receipt = receipt.read_bytes()
            base = self.root / self.api.BASE_RECORD
            before_base, before_seed = base.read_bytes(), self.seed_bytes()
            with resume.open('w') as channel:
                channel.write('resume failure\n')
            stdout, stderr = first.communicate(timeout=30)
            self.assertEqual(23, first.returncode, '[FAIL] failed_entry_preserves_native_exit: ' + stdout + stderr)
            self.assertTrue(receipt.is_file(), '[FAIL] failed_cleanup_preserves_competing_receipt')
            self.assertEqual(before_receipt, receipt.read_bytes())
            self.assertEqual(before_base, base.read_bytes(), '[FAIL] failed_cleanup_preserves_competing_base')
            self.assertEqual(producer, self.api.read_seed_base(self.root))
            self.assertTrue(self.api.seed_format(self.output)['compatible'])
            refresh = self.refresh_canonical()
            self.assertNotIn('"action":"fetch"', refresh.stdout, '[FAIL] next_entry_keeps_competing_seed')
            self.assertEqual(before_seed, self.seed_bytes())
            def archive_downloads():
                calls = [json.loads(line) for line in (self.root / 'releases/calls.jsonl').read_text().splitlines()]
                return [call for call in calls if call[:2] == ['release', 'download']
                        and call[call.index('--pattern') + 1] != 'manifest.json']
            downloads = archive_downloads()
            next_entry = self.run_entry('--cache-miss-policy', 'fetch-or-fail',
                                        '--log-dir', str(self.root / 'logs/next'), direct=True)
            self.assertEqual(0, next_entry.returncode, '[FAIL] next_entry_succeeds: ' + next_entry.stderr)
            self.assertEqual(downloads, archive_downloads(),
                             '[FAIL] next_entry_never_restores_older_release')
            self.assertEqual(head, self.api.read_seed_base(self.root))
        finally:
            os.close(read_notice)
            if first.poll() is None:
                first.kill()
            first.communicate()

    def test_competing_preparation_cannot_remove_guarded_generation(self):
        """Pin preparation itself after earlier receipt reads have completed."""
        self.canonical_release_fixture()
        receipt = publication.member(self.output, self.api.SUFFIX)
        base = self.root / self.api.BASE_RECORD
        before_receipt, before_base = receipt.read_bytes(), base.read_bytes()
        self.assertTrue(self.api.seed_format(self.output)['compatible'])
        sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
        from lean_cache_release import cache_guard
        with cache_guard(self.root):
            result = subprocess.run([sys.executable, '-B',
                str(self.root / 'tools/lean-inspector/reuse.py'), 'prepare',
                '--repository', str(self.root), '--report', str(self.output)],
                cwd=self.root, env=self.environment, text=True, capture_output=True, timeout=30)
        self.assertNotEqual(0, result.returncode,
                            '[FAIL] competing_preparation_must_not_cross_active_guard')
        self.assertTrue(receipt.is_file(), '[FAIL] competing_preparation_removed_active_receipt')
        self.assertTrue(base.is_file(), '[FAIL] competing_preparation_removed_active_base')
        self.assertEqual(before_receipt, receipt.read_bytes())
        self.assertEqual(before_base, base.read_bytes())
        self.assertFalse((self.root / 'calls').exists(), '[FAIL] competing_preparation_never_enters_lake')

    def test_reuse_failure_keeps_its_existing_receipt_and_base(self):
        self.canonical_release_fixture()
        self.fixture.write('D5/A.lean', 'def a := 1\n')
        self.script('tools/scripts/worktree/lean-cache-run.sh',
                    'printf "lake %s\\n" "$*" >> calls\nexit "${FIXTURE_PROGRAM_EXIT:-23}"\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean',
                        'tools/scripts/worktree/lean-cache-run.sh'], check=True, capture_output=True)
        self.git_commit('matching report inputs', empty=True)
        self.api.reuse(self.root, self.output, self.output)
        receipt = publication.member(self.output, self.api.SUFFIX)
        before_receipt = receipt.read_bytes()
        base = self.root / self.api.BASE_RECORD
        before_base = base.read_bytes()
        before_seed = {suffix: publication.member(self.output, suffix).read_bytes()
                       for suffix in publication.SUFFIXES}
        self.environment['STRATALINT_LEAN_BUILD_TARGETS'] = '["leanInspector/reportInspector"]'
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(23, result.returncode, '[FAIL] reuse_program_failure_propagates_exit')
        self.assertIn('phase=programs exit=23', result.stderr)
        self.assert_entry_seed_decision(result, 'keep', 'seed-current')
        self.assertTrue(receipt.is_file(), '[FAIL] reuse_program_failure_keeps_receipt')
        self.assertEqual(before_receipt, receipt.read_bytes())
        self.assertEqual(before_base, base.read_bytes(), '[FAIL] reuse_program_failure_keeps_base')
        for suffix, content in before_seed.items():
            self.assertEqual(content, publication.member(self.output, suffix).read_bytes())
        self.assertTrue(self.api.seed_format(self.output)['compatible'])
        self.assert_successful_program_reuse()
        self.assertEqual(before_receipt, receipt.read_bytes())
        self.assertEqual(before_base, base.read_bytes())

    def test_refreshed_reuse_failure_keeps_its_installed_receipt_and_base(self):
        local, producer, tag = self.canonical_release_fixture()
        # The local generation has changed inputs; the approved archive matches HEAD.
        self.fixture.bundle()
        publication.publish(self.seed, self.output, publication.coordinates(self.root), self.root)
        self.api.write_receipt(self.output, self.api.capture(self.root))
        self.write_base(local)
        self.fixture.write('D5/A.lean', 'def a := 1\n')
        self.script('tools/scripts/worktree/lean-cache-run.sh',
                    'printf "lake %s\\n" "$*" >> calls\nexit "${FIXTURE_PROGRAM_EXIT:-23}"\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean',
                        'tools/scripts/worktree/lean-cache-run.sh'], check=True, capture_output=True)
        self.git_commit('matching release inputs', empty=True)
        self.set_release_publication_mode(tag, 'cached')
        restored = self.root / 'releases' / tag / 'build/stratalint' / publication.RAW
        expected_seed = {suffix: publication.member(restored, suffix).read_bytes()
                         for suffix in (*publication.SUFFIXES, self.api.SUFFIX)}
        self.environment['STRATALINT_LEAN_BUILD_TARGETS'] = '["leanInspector/reportInspector"]'
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(23, result.returncode, '[FAIL] refreshed_program_failure_propagates_exit')
        self.assertIn('phase=programs exit=23', result.stderr)
        decision = self.assert_entry_seed_decision(result, 'fetch', 'newer-release')
        self.assertEqual((local, producer, tag), (decision['local'], decision['release'], decision['tag']))
        self.assertEqual(1, len(self.archive_downloads()), '[FAIL] refreshed_program_failure_fetches_once')
        for suffix, content in expected_seed.items():
            self.assertEqual(content, publication.member(self.output, suffix).read_bytes(),
                             '[FAIL] refreshed_program_failure_keeps_installed_bundle: ' + suffix)
        self.assertEqual(producer, self.api.read_seed_base(self.root),
                         '[FAIL] refreshed_program_failure_keeps_installed_base')
        self.assertTrue(self.api.seed_format(self.output)['compatible'])
        base = self.root / self.api.BASE_RECORD
        before_base = base.read_bytes()
        self.assert_successful_program_reuse()
        self.assertEqual(1, len(self.archive_downloads()), '[FAIL] successful_reuse_does_not_refetch')
        self.assertEqual(before_base, base.read_bytes())
        for suffix, content in expected_seed.items():
            self.assertEqual(content, publication.member(self.output, suffix).read_bytes())

    def assert_entry_seed_decision(self, result, action, reason):
        lines = [line for line in (result.stdout + result.stderr).splitlines()
                 if line.startswith('LEAN_REPORT_SEED_DECISION ')]
        self.assertEqual(1, len(lines), '[FAIL] entry_prints_seed_decision_exactly_once: '
                         + result.stdout + result.stderr)
        self.assertIn(lines[0], result.stdout, '[FAIL] completed_reuse_decision_reaches_stdout')
        decision = json.loads(lines[0].partition(' ')[2])
        self.assertEqual((action, reason), (decision['action'], decision['reason']),
                         '[FAIL] entry_prints_completed_seed_decision')
        return decision

    def assert_successful_program_reuse(self):
        self.environment['FIXTURE_PROGRAM_EXIT'] = '0'
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail',
                                '--log-dir', str(self.root / 'logs/success'), direct=True)
        self.assertEqual(0, result.returncode, '[FAIL] successful_program_reuse_completes: ' + result.stderr)
        self.assertIn('phase=programs', result.stderr)
        self.assertIn('complete-entry-reused', result.stdout)
        self.assert_entry_seed_decision(result, 'keep', 'seed-current')

    def test_reuse_failure_keeps_identical_competing_production(self):
        self.assert_reuse_failure_keeps_competing_generation('production', identical=True)

    def test_reuse_failure_keeps_different_competing_production(self):
        self.assert_reuse_failure_keeps_competing_generation('production', identical=False)

    def test_cancelled_entry_keeps_identical_competing_restore(self):
        self.assert_reuse_failure_keeps_competing_generation('restore', identical=True)

    def test_cancelled_entry_keeps_different_competing_restore(self):
        self.assert_reuse_failure_keeps_competing_generation('restore', identical=False)

    def assert_reuse_failure_keeps_competing_generation(self, replacement, *, identical):
        """Reuse hit, writer guard released, B commits, then A fails or is cancelled."""
        _, release, tag = self.canonical_release_fixture()
        self.fixture.write('D5/A.lean', 'def a := 1\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean'], check=True, capture_output=True)
        self.git_commit('matching report inputs', empty=True)
        self.prepare_production_entry()
        self.api.reuse(self.root, self.output, self.output)
        receipt = publication.member(self.output, self.api.SUFFIX)
        observed = receipt.read_bytes()
        gates = self.root / '.lake/cleanup-gates'
        gates.mkdir()
        notice, resume = gates / 'notice', gates / 'resume'
        os.mkfifo(notice)
        os.mkfifo(resume)
        helper = self.root / 'bin/guarded-programs.py'
        helper.write_text("""import os
from pathlib import Path
import sys
sys.path.insert(0, str(Path.cwd() / 'tools/scripts/worktree'))
from lean_cache_release import cache_guard
with cache_guard(Path.cwd()):
    pass
if os.environ.get('FIXTURE_DELAY_FAILURE') == '1':
    with open(os.environ['FIXTURE_NOTICE'], 'w') as channel:
        channel.write('guard released\\n')
    with open(os.environ['FIXTURE_RESUME']) as channel:
        channel.read()
    raise SystemExit(23)
""")
        self.script('tools/scripts/worktree/lean-cache-run.sh',
                    'exec ' + shlex.quote(sys.executable) + ' -B ' + shlex.quote(str(helper)) + '\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'tools/scripts/worktree/lean-cache-run.sh'],
                       check=True, capture_output=True)
        head = self.git_commit('guarded program fixture', empty=True)
        environment = dict(self.environment, FIXTURE_DELAY_FAILURE='1',
            FIXTURE_NOTICE=str(notice), FIXTURE_RESUME=str(resume),
            STRATALINT_LEAN_BUILD_TARGETS='["leanInspector/reportInspector"]')
        read_notice = os.open(notice, os.O_RDONLY | os.O_NONBLOCK)
        first = subprocess.Popen(['bash', str(self.root / 'tools/lean-inspector/inspect.sh'),
            '--repository', str(self.root), '--output', str(self.output),
            '--log-dir', str(self.root / 'logs/first'), '--cache-miss-policy', 'fetch-or-fail'],
            cwd=self.root, env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        try:
            ready, _, _ = select.select([read_notice], [], [], 30)
            self.assertTrue(ready, '[FAIL] reuse_entry_reaches_program_guard_boundary')
            self.assertEqual(b'guard released\n', os.read(read_notice, 1024))
            self.assertEqual(observed, receipt.read_bytes(), '[FAIL] first_entry_reused_existing_receipt')
            if replacement == 'restore':
                # The tests-seat probes distinguish equal and unequal valid receipt bytes.
                self.set_release_publication_mode(tag, 'cached', different=not identical)
                second = subprocess.run(['/bin/bash',
                    str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
                    'fetch', '--repository', str(self.root), '--refresh-stale',
                    '--approved-tag', tag, '--approved-producer', release],
                    cwd=self.root, env=self.environment, text=True, capture_output=True, timeout=30)
                producer = release
            else:
                if not identical:
                    artifact = self.root / '.lake/build/lean-inspector/report.zip'
                    with zipfile.ZipFile(artifact) as archive:
                        members = {name: archive.read(name) for name in archive.namelist()}
                    name = publication.RAW + '.provenance.json'
                    provenance = json.loads(members[name])
                    for origin in provenance['module_origins'].values():
                        origin['producer_sources_sha256'] = 'c' * 64
                    members[name] = json.dumps(provenance).encode()
                    with zipfile.ZipFile(artifact, 'w') as archive:
                        for name, content in members.items():
                            archive.writestr(name, content)
                second = self.run_entry('--cache-miss-policy', 'build',
                                        '--log-dir', str(self.root / 'logs/second'), direct=True)
                producer = head
            self.assertEqual(0, second.returncode,
                             '[FAIL] competing_generation_completes: ' + second.stdout + second.stderr)
            self.assertEqual(producer, self.api.read_seed_base(self.root))
            before_receipt = receipt.read_bytes()
            self.assertEqual(identical, observed == before_receipt,
                             '[FAIL] requested_receipt_identity_control')
            base = self.root / self.api.BASE_RECORD
            before_base, before_seed = base.read_bytes(), self.seed_bytes()
            if replacement == 'restore':
                os.kill(first.pid, signal.SIGTERM)
            with resume.open('w') as channel:
                channel.write('resume failure\n')
            stdout, stderr = first.communicate(timeout=30)
            self.assertEqual(143 if replacement == 'restore' else 23, first.returncode,
                             '[FAIL] failed_entry_preserves_exit: ' + stdout + stderr)
            self.assertTrue(receipt.is_file(), '[FAIL] delayed_failure_keeps_competing_receipt')
            self.assertEqual(before_receipt, receipt.read_bytes())
            self.assertEqual(before_base, base.read_bytes(), '[FAIL] delayed_failure_keeps_competing_base')
            self.assertEqual(producer, self.api.read_seed_base(self.root))
            self.assertTrue(self.api.seed_format(self.output)['compatible'])
            downloads = self.archive_downloads()
            next_entry = self.run_entry('--cache-miss-policy', 'fetch-or-fail',
                                        '--log-dir', str(self.root / 'logs/next'), direct=True)
            self.assertEqual(0, next_entry.returncode, '[FAIL] next_entry_succeeds: ' + next_entry.stderr)
            self.assertIn('complete-entry-reused', next_entry.stdout)
            self.assertEqual(downloads, self.archive_downloads(), '[FAIL] next_entry_keeps_competing_seed')
            self.assertEqual(before_seed, self.seed_bytes())
            self.assertEqual(before_base, base.read_bytes())
            self.assertEqual(producer, self.api.read_seed_base(self.root))
        finally:
            os.close(read_notice)
            if first.poll() is None:
                first.kill()
            first.communicate()

    def set_release_publication_mode(self, tag, mode, *, different=False):
        assets = self.root / 'releases' / tag
        report = assets / 'build/stratalint' / publication.RAW
        if different:
            provenance = publication.member(report, '.provenance.json')
            record = json.loads(provenance.read_text())
            for origin in record['module_origins'].values():
                origin['producer_sources_sha256'] = 'c' * 64
            provenance.write_text(json.dumps(record))
        publication.publish(report, report, publication.coordinates(self.root), self.root,
                            mode=mode, validate=False)
        self.api.write_receipt(report, self.api.capture(self.root))
        self.assertTrue(self.api.seed_format(report)['compatible'])
        archive = assets / 'lean-build.tgz'
        with tarfile.open(archive, 'w:gz') as output:
            output.add(assets / 'build', arcname='build')
        digest, size = publication.digest(archive), archive.stat().st_size
        manifest = json.loads((assets / 'manifest.json').read_text())
        manifest.update(archive_sha256=digest, archive_bytes=size)
        manifest['parts'] = [dict(name=archive.name, sha256=digest, bytes=size)]
        (assets / 'manifest.json').write_text(json.dumps(manifest))
        metadata = json.loads((assets / 'metadata.json').read_text())
        for asset in metadata['assets']:
            path = assets / asset['name']
            asset.update(digest='sha256:' + publication.digest(path), size=path.stat().st_size)
        (assets / 'metadata.json').write_text(json.dumps(metadata))

    def archive_downloads(self):
        log = self.root / 'releases/calls.jsonl'
        calls = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
        return [call for call in calls if call[:2] == ['release', 'download']
                and call[call.index('--pattern') + 1] != 'manifest.json']

    def test_prepared_failure_leaves_no_receipt_and_next_entry_recovers(self):
        self.canonical_release_fixture()
        result = self.run_entry('--cache-miss-policy', 'build', direct=True)
        self.assertEqual(23, result.returncode, '[FAIL] prepared_production_failure_propagates_exit')
        receipt = publication.member(self.output, self.api.SUFFIX)
        self.assertFalse(receipt.exists(), '[FAIL] prepared_production_failure_has_no_receipt')
        self.assertIsNone(self.api.read_seed_base(self.root))
        self.assertFalse(self.api.seed_format(self.output)['compatible'])
        downloads = self.archive_downloads()
        next_entry = self.run_entry('--cache-miss-policy', 'fetch-or-fail',
                                        '--log-dir', str(self.root / 'logs/next'), direct=True)
        self.assertEqual(23, next_entry.returncode, '[FAIL] recovered_stale_seed_reaches_lake')
        self.assertGreater(len(self.archive_downloads()), len(downloads),
                           '[FAIL] missing_receipt_takes_existing_recovery')
        self.assertIn('"status":"unpacked"', next_entry.stdout)
        self.assertFalse(receipt.exists(), '[FAIL] subsequent_prepared_failure_still_has_no_receipt')

    def test_failed_rollback_is_distinct_and_never_enters_lake(self):
        self.canonical_release_fixture()
        before, old_base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        self.inject_restore_error('rollback')
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        print('CASE ' + self._testMethodName + '\n' + result.stdout + result.stderr, flush=True)
        self.assertEqual(4, result.returncode,
                         '[FAIL] failed_rollback_must_fail_closed: ' + result.stdout + result.stderr)
        self.assertNotIn('lake ', '\n'.join(self.calls),
                         '[FAIL] failed_rollback_must_not_enter_lake')
        self.assertIn('release-rollback-failed', result.stdout + result.stderr,
                      '[FAIL] failed_rollback_must_have_distinct_receipt')
        self.assertIn('LEAN_REPORT_CACHE_INCOMPATIBLE', result.stdout + result.stderr)
        lines = [line for line in (result.stdout + result.stderr).splitlines()
                 if 'LEAN_CACHE_FETCH' in line and 'rollback-failed' in line]
        self.assertTrue(lines, '[FAIL] failed_rollback_receipt_missing')
        receipt = json.loads(lines[-1].partition(' ')[2])
        backup = Path(receipt['backup'])
        self.assertTrue(backup.is_dir(), '[FAIL] failed_rollback_backup_not_retained')
        self.assertTrue((backup / 'build').is_dir())
        self.assertTrue((backup / 'replacement').is_dir())
        self.assertTrue((backup / 'base.json').is_file())
        self.assertEqual(old_base, (backup / 'base.json').read_bytes())
        for path, data in before.items():
            self.assertEqual(data, (backup / 'build' / path).read_bytes())
        self.assertFalse((self.root / '.lake/build').exists())

    def canonical_release_fixture(self, *, damage=None):
        """History A < B < C < HEAD, with real archives and the production fetch."""
        sys.path.insert(0, str(ROOT / 'tools/scripts/worktree'))
        import lean_cache_release as transport
        subprocess.run(['git', '-C', str(self.root), 'branch', '-M', 'dev'],
                       check=True, capture_output=True)
        shutil.copy2(ROOT / 'tools/scripts/worktree/lean-cache-publish.sh',
                     self.root / 'tools/scripts/worktree/lean-cache-publish.sh')
        subprocess.run(['git', '-C', str(self.root), 'add',
                        'tools/scripts/worktree/lean-cache-publish.sh'], check=True, capture_output=True)
        older = self.git_commit('archive A', empty=True)
        local = self.git_commit('local B', empty=True)
        producer = self.git_commit('archive C', empty=True)
        shutil.copytree(self.restore, self.output.parent, dirs_exist_ok=True)
        (self.output.parent.parent / 'producer.txt').write_text('local B')
        self.write_base(local)
        self.fixture.write('D5/A.lean', 'def a := 2\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean'], check=True, capture_output=True)
        self.git_commit('current inputs', empty=True)
        self.environment['STRATALINT_LEAN_REPORT_REUSE'] = str(self.output)
        partition = transport.partition_path(self.root)
        key = transport.release_key(self.root)
        remote = self.root / 'releases'
        remote.mkdir()
        tags = []
        for index, commit in ((11, older), (12, producer)):
            tag = transport.prefix(partition, key) + f'ci-{index}-1'
            tags.append(tag)
            assets = remote / tag
            assets.mkdir()
            build = assets / 'build'
            shutil.copytree(self.restore, build / 'stratalint')
            (build / 'producer.txt').write_text(commit)
            if index == 12 and damage:
                report = build / 'stratalint' / publication.RAW
                if damage == 'format':
                    receipt = publication.member(report, '.reuse.json')
                    record = json.loads(receipt.read_text())
                    record['inputs']['report_format'] = 'incompatible-fixture-format'
                    receipt.write_text(json.dumps(record))
                else:
                    publication.member(report, '.materials.zip').unlink()
            with tarfile.open(assets / transport.ASSET, 'w:gz') as archive:
                archive.add(build, arcname='build')
            archive_bytes = (assets / transport.ASSET).read_bytes()
            digest = hashlib.sha256(archive_bytes).hexdigest()
            manifest = dict(schema='lean-release-seed-v4', partition=partition, cache_key=key,
                producer_commit_sha=commit, publication_id=f'ci-{index}-1',
                workflow_run_id=str(index), workflow_run_attempt='1',
                archive_sha256=digest, archive_bytes=len(archive_bytes),
                parts=[dict(name=transport.ASSET, sha256=digest, bytes=len(archive_bytes))])
            (assets / transport.MANIFEST).write_text(json.dumps(manifest))
            metadata = dict(draft=False, tag_name=tag, target_commitish='a' * 40,
                assets=[dict(name=name, digest='sha256:' + hashlib.sha256((assets / name).read_bytes()).hexdigest(),
                             size=(assets / name).stat().st_size)
                        for name in (transport.MANIFEST, transport.ASSET)])
            (assets / 'metadata.json').write_text(json.dumps(metadata))
        (remote / 'list.json').write_text(json.dumps([
            dict(tagName=tag, isDraft=False, createdAt=str(i)) for i, tag in enumerate(tags)]))
        self.script('bin/gh', 'exec ' + shlex.quote(sys.executable) + ' "$0.py" "$@"\n')
        (self.root / 'bin/gh.py').write_text('''import json, os, pathlib, shutil, sys
args = sys.argv[1:]
root = pathlib.Path(os.environ['FAKE_RELEASE_ROOT'])
with (root / 'calls.jsonl').open('a') as log:
    log.write(json.dumps(args) + '\\n')
if args[:2] == ['release', 'list']:
    print((root / 'list.json').read_text())
elif args[0] == 'api':
    assets = root / args[1].rsplit('/', 1)[1]
    if os.environ.get('FAKE_CHANGED_PRODUCER') and sum(
            json.loads(line)[0] == 'api' for line in (root / 'calls.jsonl').read_text().splitlines()) > 1:
        import hashlib
        manifest = json.loads((assets / 'manifest.json').read_text())
        manifest['producer_commit_sha'] = os.environ['FAKE_CHANGED_PRODUCER']
        (assets / 'manifest.json').write_text(json.dumps(manifest))
        metadata = json.loads((assets / 'metadata.json').read_text())
        metadata['assets'][0]['digest'] = 'sha256:' + hashlib.sha256((assets / 'manifest.json').read_bytes()).hexdigest()
        (assets / 'metadata.json').write_text(json.dumps(metadata))
    print((assets / 'metadata.json').read_text())
elif args[:2] == ['release', 'download']:
    tag = args[2]
    destination = pathlib.Path(args[args.index('--dir') + 1])
    for i, value in enumerate(args):
        if value == '--pattern':
            name = args[i + 1]
            if tag == os.environ.get('FAKE_ARCHIVE_FAILURE') and name != 'manifest.json':
                print('injected approved archive failure', file=sys.stderr)
                sys.exit(56)
            shutil.copyfile(root / tag / name, destination / name)
else:
    raise AssertionError(args)
''')
        self.environment.update(FAKE_RELEASE_ROOT=str(remote), GITHUB_ACTIONS='false',
            PATH=str(self.root / 'bin') + os.pathsep + self.environment['PATH'])
        return local, producer, tags[-1]


    def seed_bytes(self):
        build = self.root / '.lake/build'
        return {str(path.relative_to(build)): path.read_bytes()
                for path in build.rglob('*') if path.is_file()}


    def refresh_canonical(self):
        result = subprocess.run([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
            'refresh-stale-seed', '--repository', str(self.root)], env=self.environment,
            text=True, capture_output=True, timeout=30)
        self.assertEqual(0, result.returncode, '[FAIL] optional_refresh_continues: ' + result.stderr)
        print('CASE ' + self._testMethodName + '\n' + result.stdout, flush=True)
        return result


    def test_capture_without_release_module(self):
        self.canonical_release_fixture()
        base = (self.root / self.api.BASE_RECORD).read_bytes()
        (self.root / 'tools/scripts/worktree/lean_cache_release.py').unlink()
        snapshot = self.root / '.lake/capture.json'
        result = subprocess.run([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
            'capture', '--repository', str(self.root), '--report', str(self.output),
            '--snapshot', str(snapshot)], env=self.environment, capture_output=True, text=True)
        self.assertEqual(0, result.returncode, '[FAIL] capture_requires_no_release_module: ' + result.stderr)
        self.assertEqual(self.api.capture(self.root), json.loads(snapshot.read_text()))
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes(),
                         '[FAIL] capture_only_reads_seed_metadata')


    def test_custom_selected_seed_keeps_newer_local_bundle(self):
        local, _, _ = self.canonical_release_fixture()
        custom = self.root / '.lake/build/stratalint/custom-report.json'
        self.fixture.bundle()
        identity = publication.publish(self.seed, custom, publication.coordinates(self.root), self.root)
        self.api.seal(self.root, custom, self.api.capture(self.root), identity)
        before = {suffix: publication.member(custom, suffix).read_bytes()
                  for suffix in (*publication.SUFFIXES, self.api.SUFFIX)}
        self.fixture.write('D5/A.lean', 'def a := 3\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean'], check=True, capture_output=True)
        self.git_commit('later custom inputs', empty=True)
        self.environment.pop('STRATALINT_LEAN_REPORT_REUSE')
        result = self.run_entry('LEAN_REPORT=' + str(custom))
        self.assertIn('"reason":"non-canonical-seed"', result.stdout,
                      '[FAIL] custom_selected_seed_has_own_keep_reason: ' + result.stdout)
        self.assertNotIn('"action":"fetch"', result.stdout, '[FAIL] custom_selected_seed_never_refreshes')
        self.assertFalse((self.root / 'releases/calls.jsonl').exists(), '[FAIL] custom_seed_never_lists')
        self.assertEqual(local, self.api.read_seed_base(self.root))
        for suffix, data in before.items():
            if suffix != self.api.SUFFIX:  # The failing new production clears its own success receipt.
                self.assertEqual(data, publication.member(custom, suffix).read_bytes())


    def test_equal_raw_restore_with_different_sidecars_is_not_relabelled(self):
        _, producer, _ = self.canonical_release_fixture()
        self.fixture.write('D5/A.lean', 'def a := 1\n')
        self.fixture.write('lakefile.toml', 'name = "fixture"\n# configured production\n')
        subprocess.run(['git', '-C', str(self.root), 'add', 'D5/A.lean', 'lakefile.toml'],
                       check=True, capture_output=True)
        self.git_commit('configuration production', empty=True)
        captured = self.api.capture(self.root)
        self.fixture.bundle()
        identity = publication.publish(self.seed, self.output, publication.coordinates(self.root), self.root)
        raw_digest = publication.digest(self.output)
        sidecar = publication.member(self.output, '.provenance.json').read_bytes()
        subprocess.run(['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
            'fetch', '--repository', str(self.root), '--refresh-stale'], env=self.environment,
            capture_output=True, text=True, check=True)
        self.assertEqual(raw_digest, publication.digest(self.output))
        self.assertNotEqual(sidecar, publication.member(self.output, '.provenance.json').read_bytes())
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        try:
            self.api.seal(self.root, self.output, captured, identity)
        except ValueError as error:
            self.assertIn('generation changed', str(error))
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes(),
                         '[FAIL] equal_raw_restore_keeps_its_own_producer')
        self.assertEqual(producer, self.api.read_seed_base(self.root))
        self.assertEqual(before, self.seed_bytes(), '[FAIL] equal_raw_restore_keeps_its_own_receipt')


    def test_restore_during_canonical_publication_is_excluded(self):
        self.canonical_release_fixture()
        self.prepare_production_entry()
        source = self.root / 'tools/lean-inspector/publication.py'
        text = source.read_text()
        marker = '        destination.parent.mkdir(parents=True, exist_ok=True)'
        self.assertIn(marker, text)
        command = ['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
                   'fetch', '--repository', str(self.root), '--refresh-stale']
        hook = ('        import subprocess\n'
                '        attempt = subprocess.run(' + repr(command) + ', capture_output=True, text=True)\n'
                '        (Path(repository) / "logs/restore-during-publication.json").write_text(\n'
                '            json.dumps(dict(exit=attempt.returncode, stdout=attempt.stdout, stderr=attempt.stderr)))\n')
        source.write_text(text.replace(marker, hook + marker))
        subprocess.run(['git', '-C', str(self.root), 'add', 'tools/lean-inspector/publication.py'],
                       check=True, capture_output=True)
        head = self.git_commit('publication exclusion fixture', empty=True)
        result = self.run_entry('--cache-miss-policy', 'build', '--log-dir', str(self.root / 'logs'), direct=True)
        self.assertEqual(0, result.returncode, '[FAIL] guarded_publication_succeeds: ' + result.stderr)
        attempt = json.loads((self.root / 'logs/restore-during-publication.json').read_text())
        self.assertNotEqual(0, attempt['exit'], '[FAIL] restore_is_excluded_during_publication')
        self.assertIn('"status":"miss"', attempt['stdout'])
        self.assertEqual(head, self.api.read_seed_base(self.root), '[FAIL] active_seed_retains_production_base')
        self.assertTrue(self.api.seed_format(self.output)['compatible'])
        self.assertEqual('local B', (self.root / '.lake/build/producer.txt').read_text())

    def test_entry_propagates_seal_failure_from_publication(self):
        self.canonical_release_fixture()
        self.prepare_production_entry()
        native = self.root / 'tools/lean-inspector/native.py'
        text = native.read_text()
        marker = '        identity = public.publish(report, Path(destination), inputs, root, mode=mode, validate=False)'
        self.assertIn(marker, text)
        native.write_text(text.replace(marker, marker + '\n        (Path(root) / "D5/A.lean").write_text("def a := 9\\n")'))
        subprocess.run(['git', '-C', str(self.root), 'add', 'tools/lean-inspector/native.py'],
                       check=True, capture_output=True)
        self.git_commit('seal failure fixture', empty=True)
        result = self.run_entry('--cache-miss-policy', 'build', '--log-dir', str(self.root / 'logs'), direct=True)
        self.assertNotEqual(0, result.returncode, '[FAIL] publication_propagates_failed_seal')
        self.assertIn('LEAN_INSPECTOR_FAILED phase=publish exit=1', result.stderr)
        self.assertIn('registered inputs changed during report entry', result.stderr)
        self.assertTrue(self.output.exists())
        self.assertFalse(publication.member(self.output, self.api.SUFFIX).exists())
        self.assertFalse((self.root / self.api.BASE_RECORD).exists())


    def prepare_production_entry(self, *, restore_before_seal=False):
        self.fixture.bundle()
        produced_sha256 = publication.digest(self.seed)
        archive = self.root / '.lake/build/lean-inspector/report.zip'
        archive.parent.mkdir(parents=True, exist_ok=True)
        with zipfile.ZipFile(archive, 'w') as bundle:
            for suffix in publication.SUFFIXES:
                source = publication.member(self.seed, suffix)
                bundle.write(source, source.name)
        self.script('tools/scripts/worktree/lean-cache-run.sh', 'printf "lake %s\\n" "$*" >> calls\n')
        native = self.root / 'tools/lean-inspector/native.py'
        if restore_before_seal:
            text = native.read_text()
            marker = '        identity = public.publish(report, Path(destination), inputs, root, mode=mode, validate=False)'
            self.assertIn(marker, text)
            restore = ['/bin/bash', str(self.root / 'tools/scripts/worktree/lean-cache-publish.sh'),
                       'fetch', '--repository', str(self.root), '--refresh-stale']
            hook = ('\n        attempt = subprocess.run(' + repr(restore) + ', capture_output=True, text=True)\n'
                    '        (Path(root) / "logs/restore-before-seal.json").write_text(\n'
                    '            json.dumps(dict(exit=attempt.returncode, stdout=attempt.stdout, stderr=attempt.stderr)))')
            native.write_text(text.replace(marker, marker + hook))
        subprocess.run(['git', '-C', str(self.root), 'add', 'tools/lean-inspector/native.py',
                        'tools/scripts/worktree/lean-cache-run.sh'], check=True)
        self.git_commit('clean production fixture', empty=True)
        return produced_sha256


    def test_present_divergent_release_is_not_head_ancestor(self):
        local, _, tag = self.canonical_release_fixture()
        subprocess.run(['git', '-C', str(self.root), 'checkout', '-qb', 'divergent', local],
                       check=True, capture_output=True)
        divergent = self.git_commit('divergent release', empty=True)
        subprocess.run(['git', '-C', str(self.root), 'checkout', '-q', 'dev'],
                       check=True, capture_output=True)
        assets = self.root / 'releases' / tag
        manifest = json.loads((assets / 'manifest.json').read_text())
        manifest['producer_commit_sha'] = divergent
        (assets / 'manifest.json').write_text(json.dumps(manifest))
        metadata = json.loads((assets / 'metadata.json').read_text())
        metadata['assets'][0]['digest'] = 'sha256:' + publication.digest(assets / 'manifest.json')
        (assets / 'metadata.json').write_text(json.dumps(metadata))
        before = self.seed_bytes()
        result = self.refresh_canonical()
        self.assertIn('"reason":"release-not-head-ancestor"', result.stdout,
                      '[FAIL] present_divergent_release_is_proven_negative')
        self.assertEqual(before, self.seed_bytes())
        calls = [json.loads(line) for line in (self.root / 'releases/calls.jsonl').read_text().splitlines()]
        self.assertFalse(any('lean-build.tgz' in call for call in calls))


    def test_missing_local_base_object_keeps_seed_with_unprovable_reason(self):
        self.canonical_release_fixture()
        self.write_base('e' * 40)
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        result = self.refresh_canonical()
        self.assertIn('"reason":"local-base-ancestry-unprovable"', result.stdout,
                      '[FAIL] missing_local_base_has_unprovable_reason')
        self.assertEqual(before, self.seed_bytes())
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())

    def assert_ineligible_entry_keeps_seed(self, reason):
        before = self.seed_bytes()
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertIn('"action":"keep"', result.stdout, '[FAIL] ineligible_capture_prints_keep')
        self.assertIn('"reason":"' + reason + '"', result.stdout)
        self.assertEqual(23, result.returncode, '[FAIL] ineligible_capture_reaches_lake: ' + result.stderr)
        self.assertEqual('ensure', self.calls[0])
        self.assertTrue(self.calls[1].startswith('lake '), '[FAIL] ineligible_capture_uses_lake_path')
        self.assertFalse((self.root / 'releases/calls.jsonl').exists(), '[FAIL] ineligible_capture_never_lists')
        # Guarded preparation clears the receipt before producing a new report.
        for path, data in before.items():
            if not path.endswith(self.api.SUFFIX):
                self.assertEqual(data, self.seed_bytes()[path])
        print('CASE ' + self._testMethodName + '\n' + result.stdout, flush=True)

    def test_external_lean_options_keep_seed_and_reach_lake(self):
        self.canonical_release_fixture()
        self.environment['LEAN_OPTS'] = '-DmaxRecDepth=2048'
        self.assert_ineligible_entry_keeps_seed('external-semantic-environment')

    def test_external_lean_path_keeps_seed_and_reaches_lake(self):
        self.canonical_release_fixture()
        self.environment['LEAN_PATH'] = str(self.root / 'external')
        self.assert_ineligible_entry_keeps_seed('external-semantic-environment')

    def test_absent_execution_registration_keeps_seed_and_reaches_lake(self):
        self.canonical_release_fixture()
        del self.fixture.policy['report_execution']
        self.fixture.write_policy()
        subprocess.run(['git', '-C', str(self.root), 'add', 'lean-report-inputs.json'], check=True)
        self.git_commit('absent execution fixture', empty=True)
        self.assert_ineligible_entry_keeps_seed('execution-not-registered')

    def test_malformed_execution_registration_stays_fatal_at_entry(self):
        self.canonical_release_fixture()
        self.fixture.policy['report_execution']['tools'] = ['lake', 'shell']
        self.fixture.write_policy()
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertNotEqual(0, result.returncode, '[FAIL] malformed_registration_is_fatal')
        self.assertIn('report_execution', result.stderr)
        self.assertNotIn('LEAN_REPORT_SEED_DECISION', result.stdout)
        self.assertEqual([], self.calls, '[FAIL] malformed_registration_never_reaches_lake')

    def test_manifest_read_failure_keeps_seed_and_continues_at_entry(self):
        self.canonical_release_fixture()
        gh = self.root / 'bin/gh'
        original = gh.read_text()
        gh.write_text(original.replace('exec ',
            'if [ "$1" = api ]; then echo fixture-manifest-read-failed >&2; exit 71; fi\nexec ', 1))
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        refreshed = self.refresh_canonical()
        self.assertIn('fixture-manifest-read-failed', refreshed.stdout, '[FAIL] manifest_failure_has_receipt')
        self.assertEqual(before, self.seed_bytes(), '[FAIL] manifest_failure_preserves_seed')
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
        result = self.run_entry('--cache-miss-policy', 'fetch-or-fail', direct=True)
        self.assertEqual(23, result.returncode, '[FAIL] manifest_failure_reaches_lake')
        self.assertEqual('ensure', self.calls[0])
        self.assertTrue(self.calls[1].startswith('lake '))
        self.assertIn('"reason":"release-manifest-unavailable"', result.stdout)

    def test_shallow_unprovable_release_ancestry_keeps_seed(self):
        local, _, _ = self.canonical_release_fixture()
        head = subprocess.check_output(['git', '-C', str(self.root), 'rev-parse', 'HEAD'], text=True).strip()
        (self.root / '.git/shallow').write_text(head + '\n')
        self.assertEqual('true', subprocess.check_output(
            ['git', '-C', str(self.root), 'rev-parse', '--is-shallow-repository'], text=True).strip())
        before, base = self.seed_bytes(), (self.root / self.api.BASE_RECORD).read_bytes()
        result = self.refresh_canonical()
        self.assertIn('"reason":"release-head-ancestry-unprovable"', result.stdout,
                      '[FAIL] shallow_negative_keeps_seed')
        self.assertEqual(before, self.seed_bytes())
        self.assertEqual(base, (self.root / self.api.BASE_RECORD).read_bytes())
        self.assertEqual(local, self.api.read_seed_base(self.root))

    def test_shallow_provable_release_ancestry_installs_newer_seed(self):
        local, producer, _ = self.canonical_release_fixture()
        (self.root / '.git/shallow').write_text(local + '\n')
        self.assertEqual('true', subprocess.check_output(
            ['git', '-C', str(self.root), 'rev-parse', '--is-shallow-repository'], text=True).strip())
        result = self.refresh_canonical()
        self.assertIn('"action":"fetch"', result.stdout, '[FAIL] shallow_positive_installs_seed')
        self.assertEqual(producer, self.api.read_seed_base(self.root))
        self.assertEqual(producer, (self.root / '.lake/build/producer.txt').read_text())
