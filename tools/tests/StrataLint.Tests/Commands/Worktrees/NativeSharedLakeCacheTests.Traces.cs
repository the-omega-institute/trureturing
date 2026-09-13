namespace StrataLint.Tests;

public sealed partial class NativeSharedLakeCacheTests
{
    private const string TraceScenarios = """
verb_group, _, trace_scope = scenario.partition(':')
if verb_group in ['traces', 'report-traces', 'serial-traces']:
    command(main, 'warm-cache')
    build(reader)
    if verb_group != 'traces': prepare_helpers()
    trace_directory = shared_root / 'diagnostics'
    trace_directory.mkdir()
    trace = trace_directory / 'trace'
    xdg = P / 'trace-xdg'
    (xdg / 'git').mkdir(parents=True)
    global_config = xdg / 'git/config'
    system_config = P / 'system.gitconfig'
    targets = [('trace2.normalTarget', 'GIT_TRACE2'),
        ('trace2.eventTarget', 'GIT_TRACE2_EVENT'), ('trace2.perfTarget', 'GIT_TRACE2_PERF')]
    inputs = [('environment', name, name) for name in ['GIT_TRACE', 'GIT_TRACE_SETUP',
        'GIT_TRACE_PERFORMANCE', 'GIT_TRACE2', 'GIT_TRACE2_EVENT', 'GIT_TRACE2_PERF']]
    inputs += [(scope, key, variable) for scope in ['global', 'system-redirection'] for key, variable in targets]
    # System rows test inherited GIT_CONFIG_SYSTEM removal, not active default-system config.
    if trace_scope: inputs = [row for row in inputs if row[0] == trace_scope]
    verbs = ['ensure-cache', 'with-cache-reader', 'warm-cache'] if verb_group == 'traces' else [verb_group]
    def reset_trace(preexisting):
        if trace.exists(): trace.unlink()
        if preexisting: trace.write_text('existing diagnostic\n')
    for scope, key, variable in inputs:
        config = '[trace2]\n ' + key.split('.')[-1] + ' = ' + json.dumps(str(trace)) + '\n'
        global_config.write_text(config if scope == 'global' else '')
        system_config.write_text(config if scope == 'system-redirection' else '')
        extra = {'XDG_CONFIG_HOME': str(xdg)}
        if scope == 'system-redirection': extra['GIT_CONFIG_SYSTEM'] = str(system_config)
        if scope == 'environment': extra[variable] = str(trace)
        for preexisting in [False, True]:
            reset_trace(preexisting)
            before = snapshot(shared_root)
            raw = run(['git', 'status', '--porcelain'], reader, extra)
            assert snapshot(shared_root) != before, (scope, key, 'inactive positive control')
            reset_trace(preexisting)
            before = snapshot(shared_root)
            run(['git', 'status', '--porcelain'], reader, extra | {variable: '0'})
            unchanged(shared_root, before)
            records.append(dict(trace_control=key, scope=scope, preexisting=preexisting,
                raw_exit=raw.returncode, raw_wrote=True, explicit_zero_changed=0))
            for verb in verbs:
                reset_trace(preexisting)
                before = snapshot(shared_root)
                if verb == 'report-traces':
                    if (P / 'memo').exists(): shutil.rmtree(P / 'memo')
                    result = run(['make', 'lean-report'], reader, extra, expected=None)
                elif verb == 'serial-traces':
                    result = run(['/bin/bash', reader / 'tools/scripts/agent/serial-lean.sh', reader, '60'],
                        reader, extra, expected=None)
                else:
                    args = ['--', '/usr/bin/true'] if verb == 'with-cache-reader' else []
                    result = command(reader, verb, *args, extra=extra, expected=None)
                after = snapshot(shared_root)
                changes = sorted(p for p in before.keys() | after.keys() if before.get(p) != after.get(p))
                row = dict(trace=key, scope=scope, verb=verb, preexisting=preexisting,
                    exit=result.returncode, changed=changes, stdout=result.stdout, stderr=result.stderr)
                records.append(row)
                print(json.dumps(row), flush=True)
                # Always inspect shared state before judging downstream report/build failure.
                unchanged(shared_root, before)
                if verb == 'report-traces':
                    assert result.returncode == 2 and 'producer closure is unavailable' in result.stderr, result
                    # prepare_memo creates this only after BOTH Git calls succeed.
                    # The absent producer input fails later; keep that failure truthful.
                    assert (P / 'memo').is_dir(), 'fingerprint Git did not complete'
                else:
                    assert result.returncode == (2 if verb == 'warm-cache' else 0), result
                if verb == 'serial-traces':
                    assert 'SERIAL_LEAN status=complete' in result.stdout, result
                    assert (reader / '.lake/build/lib/lean/D5/Probe.olean').exists()
    if verb_group == 'traces':
        keys = ['GIT_SSH_COMMAND', 'GIT_ASKPASS', 'SSH_AUTH_SOCK', 'GIT_TERMINAL_PROMPT', 'GIT_OPTIONAL_LOCKS']
        values = dict(zip(keys, ['ssh -o BatchMode=yes', '/fixture/askpass', '/fixture/agent', '0', '0']))
        probe = 'import os,json; print(json.dumps({k:os.environ.get(k) for k in ' + repr(keys) + '}))'
        result = command(reader, 'with-cache-reader', '--', sys.executable, '-c', probe, extra=values)
        assert json.loads(result.stdout.splitlines()[-1]) == values
        # Exercise credential config and transport, not only environment retention.
        credential = P / 'credential-helper'
        credential.write_text('#!/bin/sh\nprintf "username=fixture\\npassword=fixture-secret\\n"\n')
        credential.chmod(0o700)
        global_config.write_text('[credential]\n helper = ' + json.dumps(str(credential)) + '\n'
            + '[fixture]\n value = ordinary-global-config\n')
        result = command(reader, 'cache-git', '--', 'config', '--get', 'fixture.value',
            extra={'XDG_CONFIG_HOME': str(xdg)})
        assert result.stdout.strip() == 'ordinary-global-config'
        fill = 'import subprocess; r=subprocess.run(["git","credential","fill"],input="protocol=https\\nhost=fixture.invalid\\n\\n",text=True,capture_output=True); assert r.returncode==0 and "password=fixture-secret" in r.stdout'
        command(reader, 'with-cache-reader', '--', sys.executable, '-c', fill,
            extra={'XDG_CONFIG_HOME': str(xdg), 'GIT_TERMINAL_PROMPT': '0'})
        result = command(reader, 'cache-git', '--', 'ls-remote', 'origin', 'refs/heads/dev')
        assert git(main, 'rev-parse', 'HEAD') in result.stdout
        command(reader, 'cache-git', '--', 'rev-parse', '--verify', 'missing-fixture-ref', expected=128)
        nul = command(reader, 'cache-git', '--', 'ls-files', '-z')
        assert nul.stdout == run(['git', 'ls-files', '-z'], reader).stdout
        assert ENV.get('HOME') == os.environ.get('HOME')
""";
}
