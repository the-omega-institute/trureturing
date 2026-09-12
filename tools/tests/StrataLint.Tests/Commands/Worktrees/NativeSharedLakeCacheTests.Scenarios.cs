namespace StrataLint.Tests;

public sealed partial class NativeSharedLakeCacheTests
{
    private const string NativeScenarios = """
if scenario == 'identity':
    command(reader, 'warm-cache', expected=2)
    denied = command(reader, 'warm-cache', extra={'GIT_DIR': str(main / '.git')}, expected=2)
    assert 'physical main' in denied.stderr
    assert not shared_root.exists() and not (reader / '.lake').exists()
    command(main, 'warm-cache')
    assert len(list((shared / 'artifacts').iterdir())) == 3
    before = snapshot(shared_root)
    keys = ['GIT_DIR', 'GIT_WORK_TREE', 'GIT_INDEX_FILE', 'GIT_CONFIG_COUNT', 'GIT_CONFIG_KEY_0',
        'GIT_CONFIG_VALUE_0', 'GIT_CONFIG_GLOBAL', 'GIT_OPTIONAL_LOCKS', 'CACHE_FIXTURE_KEEP']
    probe = 'import os,json; print(json.dumps({k:os.environ.get(k) for k in ' + repr(keys) + '}))'
    result = command(reader, 'with-cache-reader', '--', sys.executable, '-c', probe, extra={
        'GIT_DIR': str(main / '.git'), 'GIT_WORK_TREE': str(main), 'GIT_INDEX_FILE': str(P / 'foreign-index'),
        'GIT_CONFIG_COUNT': '1', 'GIT_CONFIG_KEY_0': 'core.worktree', 'GIT_CONFIG_VALUE_0': str(main),
        'GIT_CONFIG_GLOBAL': str(P / 'foreign-config'), 'GIT_OPTIONAL_LOCKS': '0', 'CACHE_FIXTURE_KEEP': 'preserved'})
    selected = json.loads(result.stdout.splitlines()[-1])
    assert selected['CACHE_FIXTURE_KEEP'] == 'preserved' and selected['GIT_OPTIONAL_LOCKS'] == '0'
    assert all(selected[key] is None for key in keys[:-2])
    unchanged(shared_root, before)
elif scenario == 'symlinks':
    command(main, 'warm-cache')
    relocated = P / 'relocated-artifacts'
    (shared / 'artifacts').rename(relocated)
    (shared / 'artifacts').symlink_to(relocated, target_is_directory=True)
    before, backing = snapshot(shared_root), snapshot(relocated)
    for optin in [False, True]:
        if optin:
            config = reader / 'lakefile.toml'
            config.write_text('enableArtifactCache = true\n' + config.read_text())
            (reader / 'Fixture.lean').write_text('def answer : Nat := 43\n')
        result = build(reader, expected=2)
        assert 'symlink' in result.stderr
        assert not (reader / '.lake/build/lib/lean/Fixture.olean').exists()
        unchanged(shared_root, before)
        unchanged(relocated, backing)
    (shared / 'artifacts').unlink()
    relocated.rename(shared / 'artifacts')
    artifact = next((shared / 'artifacts').iterdir())
    artifact.rename(P / 'relocated-file')
    artifact.symlink_to(P / 'relocated-file')
    assert 'symlink' in build(reader, expected=2).stderr
    artifact.unlink()
    (P / 'relocated-file').rename(artifact)
    command(reader, 'ensure-cache')
    # Cost observation only: the verdict never depends on elapsed time. Measure the
    # actual reader command with a hot stamp, including startup and the metadata scan.
    for extra_files in [0, 10000]:
        for i in range(extra_files): (shared / 'artifacts' / ('scan-' + str(i))).touch()
        before = snapshot(shared_root)
        started = time.monotonic()
        command(reader, 'with-cache-reader', '--', '/usr/bin/true')
        elapsed = time.monotonic() - started
        unchanged(shared_root, before)
        records.append(dict(scan_extra_files=extra_files, reader_command_seconds=elapsed))
elif scenario == 'helper':
    dependency = P / 'mathlib'
    dependency.mkdir()
    git(dependency, 'init', '-b', 'dev')
    git(dependency, 'config', 'user.email', 'fixture@example.invalid')
    git(dependency, 'config', 'user.name', 'Fixture')
    (dependency / 'lean-toolchain').write_text((main / 'lean-toolchain').read_text())
    (dependency / 'lakefile.toml').write_text('name = "mathlib"\n[[lean_lib]]\nname = "Mathlib"\n')
    (dependency / 'Mathlib.lean').write_text('import Lean.Elab.Tactic.LibrarySearch\n')
    git(dependency, 'add', '.')
    git(dependency, 'commit', '-m', 'tiny genuine Git Mathlib import')
    rev = git(dependency, 'rev-parse', 'HEAD')
    with (main / 'lakefile.toml').open('a') as f:
        f.write('\n[[require]]\nname = "mathlib"\ngit = ' + json.dumps(str(dependency)) + '\nrev = "' + rev + '"\n')
    (main / 'Fixture.lean').write_text('import Mathlib\ndef answer : Nat := 42\n')
    run([lake, 'update'], main)
    commit()
    command(main, 'warm-cache')
    helper_reader = fresh('helper-reader')
    # Launch shims delegate to the actual candidate command; no cache behavior is replaced.
    import shlex
    launch = ' '.join(shlex.quote(str(x)) for x in CLI)
    scripts = helper_reader / 'tools/scripts/worktree'
    scripts.mkdir(parents=True)
    (scripts / 'lean-cache-run.sh').write_text('#!/bin/bash\nexec ' + launch + ' with-cache-reader -- "$@"\n')
    (helper_reader / 'Makefile').write_text('lean-cache-ensure:\n\t@' + launch + ' ensure-cache\nlean:\n\t@' + launch + ' with-cache-reader -- lake build -v $(LEAN_TARGETS)\n')
    before = snapshot(shared_root)
    assert not (helper_reader / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').exists()
    for statement, exit_code, sentinel in [('theorem probe_target : True', 3, 'closed'),
        ('theorem probe_target : False', 0, 'open'), ('theorem probe_target : MissingType', 2, 'error')]:
        target = P / 'statement.txt'
        target.write_text(statement + '\n')
        result = run(['/bin/bash', pathlib.Path(repository) / 'tools/scripts/agent/bindonly-probe.sh',
            helper_reader, target, sentinel, '60'], helper_reader, expected=None)
        records.append(dict(helper_exit=result.returncode, stdout=result.stdout,
            probe=(helper_reader / ('.lake/bindonly-probe/BindOnlyProbe_' + sentinel + '.lean.out')).read_text()))
        imports = (helper_reader / ('.lake/bindonly-probe/BindOnlyProbe_' + sentinel + '.lean.ensure.log')).read_text()
        if sentinel == 'closed':
            assert 'Reused Mathlib' in imports and 'Built Mathlib' not in imports, imports
            records.append(dict(import_reused=1, import_built=0))
        assert result.returncode == exit_code, records[-1]
        assert 'BINDONLY_PROBE status=' + sentinel in result.stdout
    assert (helper_reader / '.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean').exists()
    unchanged(shared_root, before)
elif scenario == 'death':
    command(main, 'warm-cache')
    before = snapshot(shared_root)
    old_revision = git(main, 'rev-parse', 'HEAD')
    (main / 'Fixture.lean').write_text('#eval do\n  IO.FS.writeFile ".lake/entered" "entered"\n  for _ in [:2400] do\n    if (← System.FilePath.pathExists ".lake/release") then break\n    IO.sleep 50\n  IO.FS.writeFile ".lake/finished" "finished"\ndef answer : Nat := 43\n')
    commit()
    def processes():
        return [(int(parts[0]), int(parts[1]), int(parts[2]), parts[3]) for row in
            run(['ps', '-axo', 'pid=,ppid=,pgid=,command=']).stdout.splitlines()
            if len(parts := row.strip().split(None, 3)) == 4]
    def lean_writers():
        return [row for row in processes() if str(main / 'Fixture.lean') in row[3] and '/bin/lean ' in row[3]]
    def wait_for(predicate):
        deadline = time.monotonic() + 120
        while not predicate():
            if time.monotonic() >= deadline: raise TimeoutError('fixture synchronization hang')
            time.sleep(.05)
    groups = set()
    with (P / 'first.out').open('w') as stdout, (P / 'first.err').open('w') as stderr:
        first = subprocess.Popen([str(x) for x in CLI + ['warm-cache', '--path', main]], cwd=main,
            env=ENV, stdout=stdout, stderr=stderr, start_new_session=True)
        groups.add(first.pid)
        try:
            wait_for(lambda: (main / '.lake/entered').exists() or first.poll() is not None)
            assert first.poll() is None, (P / 'first.err').read_text()
            writers = lean_writers()
            assert len(writers) == 1, writers
            groups.update(row[2] for row in writers)
            first.kill()
            assert first.wait(timeout=10) == -9
            assert len(lean_writers()) == 1
            replacement = command(main, 'warm-cache', expected=2)
            assert 'busy' in replacement.stderr
            assert 'busy' in command(main, 'ensure-cache', expected=2).stderr
            assert len(lean_writers()) == 1
            old = fresh('old-reader', old_revision)
            hit = build(old)
            assert 'Reused Fixture' in hit.stdout and 'Built Fixture' not in hit.stdout
            assert len(lean_writers()) == 1
            unchanged(shared_root, before)
            (main / '.lake/release').touch()
            wait_for(lambda: (main / '.lake/finished').exists() and not lean_writers())
            wait_for(lambda: not any(row[2] in groups for row in processes()))
            command(main, 'warm-cache')
            build(fresh('recovered-reader'))
            assert not lean_writers()
            records.append(dict(parent_exit=-9, writers_after_death=1, replacement_exit=2,
                private_writer_exit=2, recovered=True, surviving_fixture_processes=0))
        finally:
            groups.update(row[2] for row in lean_writers())
            for group in groups:
                try: os.killpg(group, signal.SIGKILL)
                except ProcessLookupError: pass
            first.wait(timeout=10)
            wait_for(lambda: not any(row[2] in groups for row in processes()))
    # Also exercise a real timeout-created subgroup after both wrapper and Lake
    # leader die. Session membership must retain the private-output reservation.
    subgroup = fresh('subgroup-reader')
    groups = set()
    with (P / 'subgroup.out').open('w') as stdout, (P / 'subgroup.err').open('w') as stderr:
        first = subprocess.Popen([str(x) for x in CLI + ['with-cache-reader', '--path', subgroup,
            '--', 'lake', 'env', 'timeout', '60', 'lean', '-o', subgroup / '.lake/private.olean',
            subgroup / 'Fixture.lean']], cwd=subgroup, env=ENV, stdout=stdout, stderr=stderr, start_new_session=True)
        groups.add(first.pid)
        try:
            wait_for(lambda: (subgroup / '.lake/entered').exists() or first.poll() is not None)
            assert first.poll() is None, (P / 'subgroup.err').read_text()
            writer = next(row for row in processes() if row[3].split()[0].endswith('lean')
                and str(subgroup / 'Fixture.lean') in row[3])
            session = os.getsid(writer[0])
            assert writer[2] != session
            groups.update([session, writer[2]])
            first.kill()
            assert first.wait(timeout=10) == -9
            os.kill(session, signal.SIGKILL)
            wait_for(lambda: not any(row[2] == session for row in processes()))
            assert 'busy' in command(subgroup, 'ensure-cache', expected=2).stderr
            (subgroup / '.lake/release').touch()
            wait_for(lambda: not any(row[2] in groups for row in processes()))
            command(subgroup, 'ensure-cache')
            assert (subgroup / '.lake/private.olean').exists()
            records.append(dict(subgroup_survived_leader=True, private_writer_exit=2,
                recovered=True, surviving_fixture_processes=0))
        finally:
            for group in groups:
                try: os.killpg(group, signal.SIGKILL)
                except ProcessLookupError: pass
            first.wait(timeout=10)
            wait_for(lambda: not any(row[2] in groups for row in processes()))
elif scenario == 'native':
    command(main, 'warm-cache')
    before = snapshot(shared_root)
    hit = build(reader, extra={'LAKE_ARTIFACT_CACHE': 'true', 'LAKE_CACHE_DIR': str(P / 'wrong-cache'),
        'LAKE_RESTORE_ARTIFACTS': 'false'})
    assert 'Reused Fixture' in hit.stdout and 'Built Fixture' not in hit.stdout
    unchanged(shared_root, before)
    (reader / 'Fixture.lean').write_text('def answer : Nat := 43\n')
    miss = build(reader)
    assert 'Built Fixture' in miss.stdout
    unchanged(shared_root, before)
    config = reader / 'lakefile.toml'
    config.write_text('enableArtifactCache = true\n' + config.read_text())
    (reader / 'Fixture.lean').write_text('def answer : Nat := 44\n')
    optin = build(reader)
    assert 'LEAN_CACHE_FALLBACK' in optin.stdout
    assert list((reader / '.lake/artifact-cache/artifacts').iterdir())
    unchanged(shared_root, before)
    # Remote native mappings with absent blobs must never download into the shared store.
    blobs = {p.stem: p.read_bytes() for p in (shared / 'artifacts').iterdir()}
    for p in (shared / 'artifacts').iterdir(): p.unlink()
    for p in (shared / 'outputs').rglob('*.json'):
        mapping = json.loads(p.read_text())
        mapping.update(service='fixture-http', scope='fixture')
        p.write_text(json.dumps(mapping))
    requests = []
    class BlobServer(http.server.BaseHTTPRequestHandler):
        def do_GET(self):
            requests.append(self.path)
            blob = next((v for k, v in blobs.items() if k in self.path), None)
            self.send_response(200 if blob is not None else 404)
            self.end_headers()
            if blob is not None:
                try: self.wfile.write(blob)
                except (BrokenPipeError, ConnectionResetError): pass
        def log_message(self, *args): pass
    server = http.server.ThreadingHTTPServer(('127.0.0.1', 0), BlobServer)
    thread = threading.Thread(target=server.serve_forever)
    thread.start()
    try:
        remote = fresh('remote-reader')
        (remote / '.lake').mkdir()
        endpoint = 'http://127.0.0.1:' + str(server.server_port)
        (remote / '.lake/config.toml').write_text('[[cache.service]]\nname = "fixture-http"\nkind = "s3"\nartifactEndpoint = "' + endpoint + '"\nrevisionEndpoint = "' + endpoint + '/revisions"\n')
        before = snapshot(shared_root)
        fetched = build(remote)
        assert any(any(k in path for k in blobs) for path in requests), (requests, fetched.stdout)
        assert 'Built Fixture' in fetched.stdout
        assert not list((shared / 'artifacts').iterdir())
        unchanged(shared_root, before)
        records.append(dict(remote_http_requests=len(requests), remote_miss_local_build=True))
    finally:
        server.shutdown()
        server.server_close()
        thread.join()
print(json.dumps(dict(scenario=scenario, shared_cases_executed=True, records=records)))
""";
}
