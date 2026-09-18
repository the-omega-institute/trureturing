using System.Diagnostics;
using System.Formats.Tar;
using System.IO.Compression;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CiTransportTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CurrentSnapshotAcceptanceUsesTheRemainingOptionalWorkerWindow(bool available)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean"]);
        var root = fixture.Root;
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"lean\"", StringComparison.Ordinal)
                ? line.Replace("cache_layers = [], cache_activation = {}",
                    "cache_layers = [\"project\"], cache_activation = {project = \"stage-start\"}", StringComparison.Ordinal) : line)));
        fixture.CommitPlan();
        fixture.Write(".lake/build/new.olean", "new build output");
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2",
            ["CANDIDATE_SHA"] = fixture.Commit, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["CI_WORKFLOW_INPUTS"] = JsonSerializer.Serialize(new { candidate_sha = fixture.Commit }),
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
            ["GITHUB_OUTPUT"] = Path.Combine(root, "build/cache-output") };
        var result = SharedBuildContractTests.Process(root, "python3", ["-B", "-c", """
            import os, pathlib, subprocess, sys, time
            repository, root = map(pathlib.Path, sys.argv[1:3])
            available = sys.argv[3] == 'true'
            sys.path.insert(0, str(repository / 'tools/scripts/worktree'))
            import cache_deadline, lean_actions
            marker = root / 'build/acceptance-entered'
            def outside(*args):
                raise AssertionError('optional acceptance ran outside the bounded snapshot worker')
            lean_actions.current_lean_materials = outside
            cache_deadline.load_deadline = lambda *_: cache_deadline.CacheDeadline(
                time.monotonic() + (68 if available else 0))
            launch = subprocess.Popen
            child = '''
            import importlib.util, os, pathlib, signal, sys
            script = pathlib.Path(sys.argv[1])
            sys.path.insert(0, str(script.parent))
            spec = importlib.util.spec_from_file_location('lean_actions', script)
            owner = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(owner)
            def slow(root, *args):
                (root / 'build/acceptance-entered').write_text(str(os.getpid()))
                signal.pause()
            owner.current_lean_materials = slow
            sys.argv = [str(script), *sys.argv[2:]]
            raise SystemExit(owner.main())
            '''
            import textwrap
            def start(command, **options):
                if '--snapshot-directory' in command:
                    command = [command[0], '-B', '-c', textwrap.dedent(child), *command[1:]]
                return launch(command, **options)
            lean_actions.subprocess.Popen = start
            sys.argv = ['lean_actions.py', 'snapshot', '--repository', str(root),
                '--stage', 'current', '--layer', 'project', '--bounded-cache']
            assert lean_actions.main() == 0
            assert marker.exists() == available
            if available:
                try: os.kill(int(marker.read_text()), 0)
                except ProcessLookupError: pass
                else: raise AssertionError('timed out acceptance worker remains alive')
            assert (root / '.lake/build/new.olean').read_text() == 'new build output'
            assert not list((root / 'build').glob('.snapshot-*'))
            """, TestRepositoryLayout.FindRoot(), root, available.ToString().ToLowerInvariant()], environment,
            TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("project_ready=false", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("project_ready=true", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("dependency")]
    [InlineData("project")]
    public void HeavySnapshotRequiresThisExecutionToHaveBuiltLean(string layer)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"filemap\"", StringComparison.Ordinal)
                ? line.Replace("cache_layers = [], cache_activation = {}", "cache_layers = [\"" + layer
                    + "\"], cache_activation = {" + layer + " = \"stage-start\"}", StringComparison.Ordinal) : line)));
        fixture.CommitPlan();
        fixture.Processes(prepareReport: false);
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal("filemap", Assert.Single(CommonExecutionEvidence.ValidateCurrent(fixture.Root).Steps).Name);
        Assert.Equal(0, Run("transport-pack", fixture.Root, "current", fixture.Commit, "17", "2", Path.Combine(fixture.Root, "build/current.tgz")));
        var source = Path.Combine(fixture.Root, layer == "dependency" ? ".lake/packages" : ".lake/build", "fixture.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        File.WriteAllText(source, "existing optional seed");
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = "17", ["GITHUB_RUN_ATTEMPT"] = "2",
            ["CANDIDATE_SHA"] = fixture.Commit, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["CI_WORKFLOW_INPUTS"] = JsonSerializer.Serialize(new { candidate_sha = fixture.Commit }),
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
            ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/cache-output") };
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B",
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), "snapshot",
            "--repository", fixture.Root, "--stage", "current", "--layer", layer], environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains(layer + "_ready=false", result.Text, StringComparison.Ordinal);
        Assert.True(result.Text.Contains("current did not execute a successful Lean build", StringComparison.Ordinal), result.Text);
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, "build/lean-cache", layer)));
        Assert.Equal("existing optional seed", File.ReadAllText(source));
    }

    [Theory]
    [InlineData("lean", "valid", true)]
    [InlineData("lean", "run", false)]
    [InlineData("lean", "current", false)]
    [InlineData("lean-report", "valid", true)]
    [InlineData("lean-report", "run", false)]
    [InlineData("lean-report", "current", false)]
    public void LeanSnapshotConsumesTheAcceptedCurrentExecution(string resource, string defect, bool ready)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([resource]);
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"" + resource + "\"", StringComparison.Ordinal)
                ? line.Replace("cache_layers = [], cache_activation = {}",
                    "cache_layers = [\"project\"], cache_activation = {project = \"stage-start\"}", StringComparison.Ordinal) : line)));
        fixture.CommitPlan();
        fixture.Processes();
        using var output = new StringWriter();
        Assert.True(fixture.Run("current", output) == 0, output.ToString());
        Assert.Equal(resource, Assert.Single(CommonExecutionEvidence.ValidateCurrent(fixture.Root).Steps).Name);
        var runtime = Path.Combine(TestRepositoryLayout.FindRoot(), "tools/StrataLint.EngineeringScope/bin/Release/net10.0");
        foreach (var file in Directory.GetFiles(runtime, "*", SearchOption.AllDirectories))
        {
            var target = Path.Combine(fixture.Root, "tools/StrataLint.EngineeringScope/bin/Release/net10.0", Path.GetRelativePath(runtime, file));
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(file, target, true);
        }
        Assert.Equal(0, Run("transport-pack", fixture.Root, "current", fixture.Commit, "17", "2", Path.Combine(fixture.Root, "build/current.tgz")));
        var source = Path.Combine(fixture.Root, ".lake/build/fixture.olean");
        Directory.CreateDirectory(Path.GetDirectoryName(source)!);
        File.WriteAllText(source, "standalone build result");
        if (defect == "current") File.AppendAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.CurrentPath), "corruption");
        var environment = new Dictionary<string, string> {
            ["GITHUB_EVENT_NAME"] = "push", ["GITHUB_REF"] = "refs/heads/dev", ["GITHUB_RUN_ID"] = defect == "run" ? "18" : "17", ["GITHUB_RUN_ATTEMPT"] = "2",
            ["CANDIDATE_SHA"] = fixture.Commit, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["CI_WORKFLOW_INPUTS"] = JsonSerializer.Serialize(new { candidate_sha = fixture.Commit }),
            ["GITHUB_REPOSITORY"] = Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "",
            ["STRATALINT_CACHE_WRITES"] = "true", ["STRATALINT_CHECK_SUCCEEDED"] = "true",
            ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/cache-output") };
        var result = SharedBuildContractTests.Process(fixture.Root, "python3", ["-B",
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), "snapshot",
            "--repository", fixture.Root, "--stage", "current", "--layer", "project"], environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("project_ready=" + ready.ToString().ToLowerInvariant(), result.Text, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, "build/lean-cache/project")));
        Assert.Equal("standalone build result", File.ReadAllText(source));
        Assert.Equal(resource == "lean-report", File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.ReportPath)));
    }

}
