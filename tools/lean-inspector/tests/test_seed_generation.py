"""Complete canonical generations, selected seeds, and restore exclusion contracts."""
import hashlib
import json
import os
import shlex
import shutil
import subprocess
import sys
import tarfile
import zipfile

import test_reuse
import publication

ROOT = test_reuse.ROOT


class SeedGenerationTests:
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
        (self.root / 'tools/scripts/worktree/lean_cache_release.py').unlink()
        snapshot = self.root / '.lake/capture.json'
        result = subprocess.run([sys.executable, '-B', str(self.root / 'tools/lean-inspector/reuse.py'),
            'capture', '--repository', str(self.root), '--report', str(self.output),
            '--snapshot', str(snapshot)], env=self.environment, capture_output=True, text=True)
        self.assertEqual(0, result.returncode, '[FAIL] capture_requires_no_release_module: ' + result.stderr)
        self.assertEqual(self.api.capture(self.root), json.loads(snapshot.read_text()))
        self.assertFalse((self.root / self.api.BASE_RECORD).exists())


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
        # Capture clears the receipt before a new production, leaving the seed bytes intact.
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
