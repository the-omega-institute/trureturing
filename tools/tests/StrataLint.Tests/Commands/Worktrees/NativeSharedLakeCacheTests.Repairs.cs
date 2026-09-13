namespace StrataLint.Tests;

public sealed partial class NativeSharedLakeCacheTests
{
    private const string CallbackScenarios = """
if scenario.startswith('callbacks:'):
    origin = scenario.split(':')[1]
    prepare_helpers()
    # The queried repository differs from the actual helper's script root/CWD.
    query_main = P / 'query-main'
    git(main, 'clone', main, query_main)
    target = P / 'callback-target'
    git(query_main, 'worktree', 'add', '--detach', target, 'HEAD')
    runner_shared = shared_root
    target_shared = query_main / '.git/stratalint-lake'
    runner_shared.mkdir()
    target_shared.mkdir()
    private = P / 'private-diagnostic'
    hook = P / 'fsmonitor-hook'
    child = P / 'diagnostic-child'
    # Valid protocol v2, conservative all-dirty response. Both the callback and
    # its ordinary subprocess log to the configured (possibly stale) destination.
    child.write_text('#!/bin/sh\nprintf "child query\\n" >> "$FSMONITOR_LOG"\n')
    child.chmod(0o700)
    hook.write_text('#!/bin/sh\n/bin/mkdir -p "${FSMONITOR_LOG%/*}"\nprintf "hook query\\n" >> "$FSMONITOR_LOG"\n'
        + '/bin/sh "$FSMONITOR_CHILD"\nprintf "fixture-token\\000/\\000"\n')
    hook.chmod(0o700)
    xdg = P / 'callback-xdg'
    (xdg / 'git').mkdir(parents=True)
    config = '[core]\n fsmonitor = ' + json.dumps(str(hook)) + '\n fsmonitorHookVersion = 2\n'
    if origin == 'global': (xdg / 'git/config').write_text(config)
    elif origin == 'repository':
        for root in [main, query_main]:
            git(root, 'config', 'core.fsmonitor', str(hook))
            git(root, 'config', 'core.fsmonitorHookVersion', '2')
    else:
        for root in [main, query_main]: git(root, 'config', 'extensions.worktreeConfig', 'true')
        git(target, 'config', '--worktree', 'core.fsmonitor', str(hook))
        git(target, 'config', '--worktree', 'core.fsmonitorHookVersion', '2')
    (query_main / 'dirty').write_text('admission must stop after status\n')
    if origin == 'worktree':
        git(query_main, 'config', '--worktree', 'core.fsmonitor', str(hook))
        git(query_main, 'config', '--worktree', 'core.fsmonitorHookVersion', '2')
    unused_lake = P / 'unused-lake'
    unused_lake.write_text('#!/bin/sh\nprintf called > "' + str(P / 'lake-called') + '"\nexit 89\n')
    unused_lake.chmod(0o700)
    extra = {'XDG_CONFIG_HOME': str(xdg), 'FSMONITOR_LOG': str(private),
        'FSMONITOR_CHILD': str(child), 'GIT_OPTIONAL_LOCKS': '0',
        'LAKE_BIN': str(unused_lake), 'ELAN_HOME': str(P / 'no-toolchains')}
    status = ['status', '--porcelain=v1', '-z', '--untracked-files=all']
    index = ['ls-files', '-s', '-z']
    # Initialize the real index's fsmonitor extension without materializing Lake.
    run(['git', 'update-index', '--fsmonitor'], target, extra)
    shell = reader / 'tools/scripts/worktree/lean-cache-run.sh'
    queries = [('status', CLI + ['cache-git', '--path', target, '--', *status], 0),
        ('index', CLI + ['cache-git', '--path', target, '--', *index], 0),
        ('shell-status', [shell, '--git', '-C', target, *status], 0),
        ('shell-index', [shell, '--git', '-C', target, *index], 0),
        ('input-address', [reader / 'tools/scripts/worktree/lean-cache-input.sh',
            'dependency-address', '--repository', target], 0),
        ('make-report', ['make', '-f', reader / 'Makefile', 'lean-report'], 2),
        ('warm-admission', CLI + ['warm-cache', '--path', query_main], 2)]
    # The make row uses its actual repository-relative recipe in the script root.
    if origin == 'worktree':
        git(reader, 'config', '--worktree', 'core.fsmonitor', str(hook))
        git(reader, 'config', '--worktree', 'core.fsmonitorHookVersion', '2')
    run(['git', 'update-index', '--fsmonitor'], reader, extra)
    def reset_log(preexisting):
        if diagnostic.exists(): diagnostic.unlink()
        if preexisting: diagnostic.write_text('existing diagnostic\n')
    for preexisting in [False, True]:
        for name, args, expected in queries:
            cwd = reader if name == 'make-report' else query_main if name == 'warm-admission' else target
            shared_root = runner_shared if name == 'make-report' else target_shared
            diagnostic = shared_root / 'diagnostic'
            # A sensitive raw control for the exact index/status refresh.
            raw_args = index if name in ['index', 'shell-index'] else status
            reset_log(preexisting)
            before = snapshot(shared_root)
            run(['git', *raw_args], cwd, extra | {'FSMONITOR_LOG': str(diagnostic)})
            assert snapshot(shared_root) != before, (name, 'raw callback inactive')
            assert 'hook query\nchild query\n' in diagnostic.read_text()
            reset_log(preexisting)
            before = snapshot(shared_root)
            expected_bytes = run(['git', '-c', 'core.fsmonitor=false', *raw_args], cwd,
                extra | {'FSMONITOR_LOG': str(diagnostic)}).stdout
            unchanged(shared_root, before)
            if private.exists(): private.unlink()
            control = run(args, cwd, extra, expected=expected)
            assert private.exists(), (name, 'private callback absent', control)
            assert 'hook query\nchild query\n' in private.read_text(), (name, 'private callback suppressed')
            if (P / 'memo').exists(): shutil.rmtree(P / 'memo')
            before = snapshot(shared_root)
            result = run(args, cwd, extra | {'FSMONITOR_LOG': str(diagnostic)}, expected=None)
            row = dict(callback=name, origin=origin, preexisting=preexisting,
                exit=result.returncode, stdout=result.stdout, stderr=result.stderr,
                raw_positive=True, private_callback=True, explicit_false_changed=0)
            records.append(row)
            print(json.dumps(row), flush=True)
            unchanged(shared_root, before)
            assert result.returncode == expected, row
            if name in ['status', 'index', 'shell-status', 'shell-index']:
                assert result.stdout == expected_bytes, row
            if name == 'warm-admission': assert 'clean checkout' in result.stderr, row
            if name == 'make-report':
                assert 'producer closure is unavailable' in result.stderr, row
            if name in ['input-address', 'make-report']:
                assert (P / 'memo').is_dir(), 'fingerprint Git did not complete'
            assert not (target / '.lake').exists() and not (reader / '.lake').exists()
            assert not (P / 'no-toolchains').exists() and not (P / 'lake-called').exists()
            assert not (main / '.git/stratalint-lake-locks').exists()
    # Native selection and bytes: options locate a different common directory.
    shared_root = target_shared
    before = snapshot(shared_root)
    selectors = [['-C', str(P), '-C', '', '-C', target.name],
        ['-c', 'fixture.value=ordinary', '-C', str(target)],
        ['--config-env', 'fixture.value=FSMONITOR_LOG', '-C', str(target)],
        ['--git-dir', git(target, 'rev-parse', '--absolute-git-dir'), '--work-tree', str(target)],
        ['--git-dir=' + git(target, 'rev-parse', '--absolute-git-dir'), '--work-tree=' + str(target)]]
    for options in selectors:
        actual = command(reader, 'cache-git', '--', *options, *status, extra=extra | {'FSMONITOR_LOG': str(diagnostic)})
        assert actual.stdout == run(['git', *options, '-c', 'core.fsmonitor=false', *status], reader, extra).stdout
        unchanged(shared_root, before)
    args = ['-C', str(target), 'ls-tree', '-rz', 'HEAD']
    assert command(reader, 'cache-git', '--', *args, extra=extra).stdout == run(['git', *args], reader, extra).stdout
    for args in [['-C', str(target), 'rev-parse', '--verify', 'absent'], ['-C']]:
        raw = run(['git', *args], reader, extra, expected=None)
        actual = command(reader, 'cache-git', '--', *args, extra=extra, expected=raw.returncode)
        assert actual.stdout == raw.stdout and actual.stderr == raw.stderr
    unchanged(shared_root, before)
    # Bootstrap still works with no Lean pins, installed toolchain or writer lock.
    (target / 'lean-toolchain').unlink()
    (target / 'lake-manifest.json').unlink()
    command(reader, 'cache-git', '--', '-C', target, *status, extra=extra)
    assert not (target / '.lake').exists()
    # Admission is shared with native readers and never repairs stale topology.
    alias = P / 'outside-alias'
    blob = target_shared / 'blob'
    blob.write_text('shared bytes')
    os.link(blob, alias)
    before = snapshot(target_shared)
    failed = command(reader, 'cache-git', '--', '-C', target, *status, extra=extra, expected=2)
    assert 'hardlink' in failed.stderr
    unchanged(target_shared, before)
    alias.unlink()
    diagnostic = target_shared / 'diagnostic'
    link = target_shared / 'symbolic'
    link.symlink_to(private)
    before = snapshot(target_shared)
    failed = command(reader, 'cache-git', '--', '-C', target, *status, extra=extra, expected=2)
    assert 'symlink' in failed.stderr
    unchanged(target_shared, before)
    # An absent namespace is protected too; the owner removes only fixture files.
    shutil.rmtree(target_shared)
    before = snapshot(target_shared)
    command(reader, 'cache-git', '--', '-C', target, *status,
        extra=extra | {'FSMONITOR_LOG': str(diagnostic)})
    unchanged(target_shared, before)
    run(['git', *status], target, extra | {'FSMONITOR_LOG': str(diagnostic)})
    assert 'hook query\nchild query\n' in diagnostic.read_text()
""";

    private const string RepairScenarios = """
if scenario == 'hardlinks':
    command(main, 'warm-cache')
    before = snapshot(shared_root)
    hit = build(reader)
    assert 'Reused Fixture' in hit.stdout and 'Built Fixture' not in hit.stdout
    unchanged(shared_root, before)
    artifact = next((shared / 'artifacts').glob('*.olean'))
    private = reader / '.lake/build/lib/lean/Fixture.olean'
    # Inject stale topology explicitly; fresh native reads above never make this alias.
    private.unlink()
    os.link(artifact, private)
    before = snapshot(shared_root)
    result = command(reader, 'with-cache-reader', '--', 'lake', 'clean', expected=None)
    after = snapshot(shared_root)
    changes = [p for p in before.keys() | after.keys() if before.get(p) != after.get(p)]
    records.append(dict(stale_hardlink_injected=True, supported_action='lake clean',
        exit=result.returncode, changed=changes, private_alias_exists=private.exists()))
    print(json.dumps(records[-1]))
    assert result.returncode == 2 and 'hardlink' in result.stderr, result
    unchanged(shared_root, before)
    assert private.exists() and private.stat().st_nlink == 2
    # Maintenance belongs to the fixture owner, outside the reader boundary.
    private.unlink()
    before = snapshot(shared_root)
    command(reader, 'with-cache-reader', '--', 'lake', 'clean')
    hit = build(reader)
    assert 'Reused Fixture' in hit.stdout and 'Built Fixture' not in hit.stdout
    unchanged(shared_root, before)
    # An alias outside the active partition is equally unsafe for private commands.
    inactive = shared_root / 'inactive'
    inactive.mkdir()
    (inactive / 'blob').write_text('inactive artifact')
    os.link(inactive / 'blob', reader / '.lake/stale')
    before = snapshot(shared_root)
    assert 'hardlink' in command(reader, 'ensure-cache', expected=2).stderr
    unchanged(shared_root, before)
elif scenario == 'dependencies':
    dependency = P / 'dependency'
    dependency.mkdir()
    git(dependency, 'init', '-b', 'dev')
    git(dependency, 'config', 'user.email', 'fixture@example.invalid')
    git(dependency, 'config', 'user.name', 'Fixture')
    (dependency / 'lakefile.toml').write_text('name = "dependency"\n')
    (dependency / 'Dependency.lean').write_text('def dependencyAnswer : Nat := 7\n')
    git(dependency, 'add', '.')
    git(dependency, 'commit', '-m', 'genuine Git dependency')
    rev = git(dependency, 'rev-parse', 'HEAD')
    with (main / 'lakefile.toml').open('a') as f:
        f.write('\n[[require]]\nname = "dependency"\ngit = ' + json.dumps(str(dependency)) + '\nrev = "' + rev + '"\n')
    run([lake, 'update'], main)
    commit()
    command(main, 'warm-cache')
    target = fresh('dependency-reader')
    command(target, 'ensure-cache')
    stamp = target / '.lake/.stratalint-lean-cache-stamp.json'
    saved_stamp = stamp.read_bytes()
    package = target / '.lake/packages/dependency'
    assert git(package, 'rev-parse', 'HEAD') == rev
    output = target / '.lake/build/unrelated.olean'
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text('unrelated private output')
    saved_output = snapshot(output.parent)
    shutil.rmtree(package)
    before = snapshot(shared_root)
    result = command(target, 'ensure-cache')
    print(json.dumps(dict(standalone_exit=result.returncode, source_restored=package.exists(), stamp_retained=stamp.read_bytes() == saved_stamp)))
    assert package.exists(), 'matching stamp suppressed live materialization'
    assert git(package, 'rev-parse', 'HEAD') == rev
    assert stamp.read_bytes() == saved_stamp
    assert snapshot(output.parent) == saved_output
    unchanged(shared_root, before)
    shutil.rmtree(package)
    dependency.rename(P / 'dependency-unavailable')
    failed = command(target, 'ensure-cache', expected=2)
    assert 'Lake dependency materialization failed' in failed.stderr
    assert snapshot(output.parent) == saved_output
    unchanged(shared_root, before)
elif scenario == 'stale-session':
    command(reader, 'ensure-cache')
    lock = next((main / '.git/stratalint-lake-locks').glob('*.lock'))
    unrelated = subprocess.Popen(['/bin/sleep', '120'], start_new_session=True, env=ENV)
    try:
        # Deterministic stale-record fixture, not a forced kernel PID wrap.
        lock.write_text(str(unrelated.pid) + '\n')
        result = command(reader, 'ensure-cache', expected=None)
        print(json.dumps(dict(numeric_stale_record=True, unrelated_pid=unrelated.pid, exit=result.returncode)))
        # Old identity-free records must fail truthfully, not masquerade as live writers.
        assert result.returncode == 2 and 'identity' in result.stderr
        lock.write_text('')
        # Obtain a real reservation, then simulate numeric ID reuse after its writer exits.
        reservation = P / 'reservation'
        probe = 'import pathlib; pathlib.Path(' + repr(str(reservation)) + ').write_bytes(pathlib.Path(' + repr(str(lock)) + ').read_bytes())'
        command(reader, 'with-cache-reader', '--', sys.executable, '-c', probe)
        record = reservation.read_text().split()
        assert len(record) == 2
        record[0] = str(unrelated.pid)
        lock.write_text(' '.join(record) + '\n')
        command(reader, 'ensure-cache')
        assert unrelated.poll() is None
        # Same stale session number with an old boot identity is also recoverable.
        identity = record[1].split(':')
        identity[0] = '00000000-0000-0000-0000-000000000000'
        lock.write_text(record[0] + ' ' + ':'.join(identity) + '\n')
        command(reader, 'ensure-cache')
        assert unrelated.poll() is None
        records.append(dict(simulated_pid_reuse=True, stale_boot=True, recovered=True, unrelated_still_live=True))
    finally:
        unrelated.kill()
        unrelated.wait(timeout=10)
""";
}
