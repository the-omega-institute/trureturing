using System.Text;
using StrataLint.Cli;
using Xunit.Abstractions;

namespace StrataLint.Tests;

[Collection("Lean cache environment")]
public sealed partial class NativeSharedLakeCacheTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData("identity")]
    [InlineData("native")]
    [InlineData("symlinks")]
    [InlineData("helper")]
    [InlineData("death")]
    [InlineData("hardlinks")]
    [InlineData("traces")]
    [InlineData("report-traces:environment")]
    [InlineData("report-traces:global")]
    [InlineData("report-traces:system-redirection")]
    [InlineData("serial-traces:environment")]
    [InlineData("serial-traces:global")]
    [InlineData("serial-traces:system-redirection")]
    [InlineData("callbacks:repository")]
    [InlineData("callbacks:global")]
    [InlineData("callbacks:worktree")]
    [InlineData("dependencies")]
    [InlineData("stale-session")]
    public void RealEntrypointsPreserveCacheBoundaries(string scenario)
    {
        using var temporary = new TemporaryDirectory();
        // Other platforms execute the private/fail-closed controls in the same program.
        Assert.True(LeanLakeExecutable.TryResolve(out var lake, out var reason), reason);
        var script = Path.Combine(temporary.Path, "native.py");
        File.WriteAllText(script, NativeProgram + "\n" + RepairScenarios + "\n" + TraceScenarios + "\n" + CallbackScenarios + "\n" + NativeScenarios);
        var result = TestProcessRunner.Run("python3", [script, scenario,
            typeof(Program).Assembly.Location, lake, TestRepositoryLayout.FindRoot()],
            temporary.Path, TestBudgets.ReportSupervisorHangGuard, 1024 * 1024);
        var diagnostic = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        output.WriteLine(diagnostic);
        Assert.True(result.ExitCode == 0, diagnostic);
    }

    private const string NativeProgram = """
import os, sys, subprocess, pathlib, json, hashlib, shutil, signal, time, threading, http.server, platform
P = pathlib.Path(__file__).resolve().parent
scenario, assembly, lake, repository = sys.argv[1:]
CLI = [shutil.which('dotnet'), assembly, 'worktree']
ENV = os.environ.copy()
ENV['LAKE_BIN'] = lake
ENV['ELAN_TOOLCHAIN'] = 'leanprover/lean4:v4.33.0'
for key in list(ENV):
    if key.startswith('GIT_') or key.startswith('LAKE_') and key != 'LAKE_BIN': del ENV[key]
supported = sys.platform == 'darwin' and pathlib.Path('/usr/bin/sandbox-exec').exists()
records = []
def run(args, cwd=P, extra=None, expected=0):
    env = ENV | (extra or {})
    result = subprocess.run([str(x) for x in args], cwd=cwd, env=env, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=120)
    if expected is not None: assert result.returncode == expected, (args, result.returncode, result.stdout, result.stderr)
    return result
def git(root, *args): return run(['git', *args], root).stdout.strip()
def command(root, verb, *args, extra=None, expected=0):
    result = run(CLI + [verb, '--path', root, *args], root, extra, expected)
    records.append(dict(verb=verb, root=root.name, exit=result.returncode, stdout=result.stdout, stderr=result.stderr))
    return result
def build(root, **kwargs): return command(root, 'with-cache-reader', '--', 'lake', 'build', '-v', **kwargs)
def snapshot(root):
    result = {}
    if root.exists():
        for path in [root, *sorted(root.rglob('*'))]:
            st = path.lstat()
            result[str(path.relative_to(root))] = [st.st_mode, st.st_size, st.st_mtime_ns,
                st.st_ctime_ns, st.st_nlink, st.st_ino,
                hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None]
    return result
def unchanged(root, before):
    after = snapshot(root)
    changed = [p for p in before.keys() | after.keys() if before.get(p) != after.get(p)]
    assert not changed, changed
    records.append(dict(shared_entries_compared=len(before), changed=0))
def commit():
    git(main, 'add', '.')
    git(main, 'commit', '-m', 'fixture state')
    git(main, 'push', '-u', 'origin', 'dev')
def fresh(name, revision='HEAD'):
    root = P / name
    git(main, 'worktree', 'add', '--detach', root, revision)
    return root
def prepare_helpers():
    source = pathlib.Path(repository)
    # Actual make/helper scripts and candidate sources, independently built in this
    # tiny fixture. No substitute shell entrypoint, dotnet shim or repository Lean build.
    for path in (source / 'tools/scripts').rglob('*.sh'):
        target = reader / path.relative_to(source)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
    shutil.copytree(source / 'tools/lean-inspector', reader / 'tools/lean-inspector',
        ignore=shutil.ignore_patterns('__pycache__'))
    shutil.copy2(source / 'Makefile', reader / 'Makefile')
    for name in ['StrataLint.Cli', 'StrataLint.Engine', 'StrataLint.Scribe',
            'StrataLint.Scribe.Documents', 'Trureturing.Truth', 'Architecture']:
        shutil.copytree(source / 'tools' / name, reader / 'tools' / name,
            ignore=shutil.ignore_patterns('bin', 'obj'))
    for name in ['Directory.Build.props', 'Directory.Build.targets', 'Directory.Packages.props', 'global.json']:
        if (source / name).exists(): shutil.copy2(source / name, reader / name)
    (reader / 'D5').mkdir()
    (reader / 'D5/Probe.lean').write_text('def serialAnswer : Nat := 7\n')
    (reader / 'Trureturing.lean').write_text('import Fixture\n')
    with (reader / 'lakefile.toml').open('a') as f:
        f.write('\n[[lean_lib]]\nname = "D5"\nroots = ["D5.Probe"]\n')
    git(reader, 'add', '.')
    git(reader, 'commit', '-m', 'actual helper fixture')
    ENV['MSBUILDDISABLENODEREUSE'] = '1'
    ENV['DOTNET_CLI_USE_MSBUILD_SERVER'] = '0'
    ENV['STRATALINT_LEAN_INPUT_MEMO_ROOT'] = str(P / 'memo')
    ENV['STRATALINT_REPORT_CACHE_ROOT'] = str(P / 'report-cache')
    ENV['XDG_CACHE_HOME'] = str(P / 'xdg-cache')
    project = reader / 'tools/StrataLint.Cli/StrataLint.Cli.csproj'
    run(['dotnet', 'restore', project, '--locked-mode', '--disable-parallel'], reader)
    run(['dotnet', 'build', project, '--no-restore', '-c', 'Release', '--warnaserror', '-m:1', '-nodeReuse:false'], reader)
main = P / 'main with spaces'
main.mkdir()
git(main, 'init', '-b', 'dev')
git(main, 'config', 'user.email', 'fixture@example.invalid')
git(main, 'config', 'user.name', 'Fixture')
(main / 'lean-toolchain').write_text('leanprover/lean4:v4.33.0\n')
(main / 'lakefile.toml').write_text('name = "fixture"\ndefaultTargets = ["Fixture"]\n[[lean_lib]]\nname = "Fixture"\n')
(main / 'lake-manifest.json').write_text('{"version":"1.2.0","packagesDir":".lake/packages","packages":[],"name":"fixture","lakeDir":".lake"}\n')
(main / 'Fixture.lean').write_text('def answer : Nat := 42\n')
(main / '.gitignore').write_text('.lake/\n')
git(main, 'init', '--bare', P / 'remote.git')
git(main, 'remote', 'add', 'origin', P / 'remote.git')
commit()
reader = fresh('reader')
shared_root = main / '.git/stratalint-lake'
shared = shared_root / ('lean-4.33.0/macos-' + ('arm64' if platform.machine() == 'arm64' else 'x64'))
if not supported:
    build(reader)
    assert (reader / '.lake/build/lib/lean/Fixture.olean').exists()
    assert not shared_root.exists()
    shared_root.mkdir()
    denied = build(reader, expected=2)
    assert 'verified read-only process guard' in denied.stderr
    command(main, 'warm-cache', expected=2)
    assert not list(shared_root.iterdir())
    print(json.dumps(dict(scenario=scenario, shared_cases_executed=False, private_and_fail_closed=True, records=records)))
    sys.exit(0)
""";
}
