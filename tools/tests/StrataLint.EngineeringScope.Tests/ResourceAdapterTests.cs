using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed partial class ResourceAdapterTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void IdleStageDoesNotHideWorkInAnotherRegisteredStage(bool otherWork)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(otherWork ? ["filemap"] : []);
        var environment = EnvironmentFor(fixture);
        MaterializePlan(fixture, environment);

        var result = Route(fixture, "engineering", environment);

        Assert.True(result.Exit == 0, result.Text);
        var lines = File.ReadAllLines(Path.Combine(fixture.Root, "build/adapter-output"));
        Assert.Contains("required=false", lines);
        Assert.Contains("work_required=" + (otherWork ? "true" : "false"), lines);
    }

    [Theory]
    [InlineData("build")]
    [InlineData("engineering")]
    [InlineData("current")]
    [InlineData("delta")]
    public void ShellNoWorkNeedsNoSdkOrCacheAndProducesSummary(string stage)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        if (stage == "delta") fixture.PrPlan();
        var environment = EnvironmentFor(fixture);
        var basis = JsonNode.Parse(File.ReadAllText(fixture.Plan))!["base"]?.ToString();
        var result = Shell(fixture, [stage, .. basis is null ? Array.Empty<string>() : [basis]], environment);
        Assert.True(result.Exit == 0, result.Text);
        var summary = Summary(fixture, stage);
        Assert.Equal("not-required", summary["status"]!.ToString());
        Assert.Equal(fixture.Commit, summary["git_candidate"]!["commit"]!.ToString());
        Assert.Empty(summary["steps"]!.AsArray());
        Assert.Empty(summary["artifacts"]!.AsArray());
        Assert.Contains("CI_STAGE_RESULT stage=" + stage + " exit=0", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("current", "extra")]
    [InlineData("engineering", "--bad")]
    [InlineData("build", "extra")]
    [InlineData("delta", "missing")]
    [InlineData("delta", "empty")]
    [InlineData("delta", "symbolic")]
    [InlineData("delta", "unavailable")]
    [InlineData("delta", "tree")]
    [InlineData("delta", "blob")]
    public void InvalidStageInputCannotBeHiddenByNoWork(string stage, string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.PrPlan();
        var value = defect switch
        {
            "empty" => "",
            "symbolic" => "HEAD",
            "unavailable" => new string('a', 40),
            "tree" => SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^{tree}"),
            "blob" => SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD:fixtures/selected.txt"),
            _ => defect,
        };
        var result = Shell(fixture, defect == "missing" ? [stage] : [stage, value], EnvironmentFor(fixture));
        Assert.Equal(2, result.Exit);
        Assert.DoesNotContain("status\": \"not-required\"", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("missing-changes")]
    [InlineData("malformed")]
    [InlineData("candidate")]
    [InlineData("scope-candidate")]
    [InlineData("scope-truncated")]
    [InlineData("scope-duplicate")]
    [InlineData("prerequisite")]
    public void WorkflowRouteFailsClosedBeforeSetup(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var environment = EnvironmentFor(fixture);
        fixture.PrPlan();
        MaterializePlan(fixture, environment);
        if (defect == "missing") File.Delete(environment["CI_PLAN_PATH"]);
        if (defect == "missing-changes") File.Delete(environment["CI_CHANGES_PATH"]);
        if (defect == "malformed") File.WriteAllText(environment["CI_PLAN_PATH"], "not json!");
        if (defect == "candidate")
        {
            var plan = JsonNode.Parse(File.ReadAllText(fixture.Plan))!;
            plan["candidate"]!["commit"] = new string('a', 40);
            File.WriteAllText(environment["CI_PLAN_PATH"], plan.ToJsonString());
        }
        if (defect.StartsWith("scope-", StringComparison.Ordinal))
        {
            var scope = JsonNode.Parse(File.ReadAllText(fixture.Changes))!;
            if (defect == "scope-candidate") scope["candidate"]!["commit"] = new string('a', 40);
            else
            {
                var rows = scope["changes"]!.AsArray();
                if (defect == "scope-truncated") rows.Clear();
                else rows.Add(rows[0]!.DeepClone());
                scope["change_count"] = rows.Count;
            }
            File.WriteAllText(environment["CI_CHANGES_PATH"], scope.ToJsonString());
        }
        if (defect == "prerequisite") environment["CI_NEEDS"] = "{\"build\":{\"result\":\"failure\",\"outputs\":{}}}";
        var result = Route(fixture, "engineering", environment);
        Assert.Equal(2, result.Exit);
        Assert.Equal("failed", Summary(fixture, "engineering")["status"]!.ToString());
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/adapter-output")));
    }

    [Theory]
    [InlineData("none")]
    [InlineData("filemap")]
    public void MaterializedRouteRequestsOnlyRegisteredStageToolsAndCaches(string resource)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(resource == "none" ? [] : [resource]);
        var filemap = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        filemap = filemap.Replace("tools = [], cache_layers = [], cache_activation = {}", "tools = [\"dotnet\"], cache_layers = [\"current\"], cache_activation = {current = \"stage-start\"}", StringComparison.Ordinal);
        fixture.Write("Meta/FILEMAP.toml", filemap);
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        MaterializePlan(fixture, environment);
        var result = Route(fixture, "current", environment);
        Assert.True(result.Exit == 0, result.Text);
        var outputs = File.ReadAllLines(Path.Combine(fixture.Root, "build/adapter-output"));
        Assert.Contains("required=" + (resource == "none" ? "false" : "true"), outputs);
        Assert.Contains("dotnet=" + (resource == "none" ? "false" : "true"), outputs);
        Assert.Contains("lake=false", outputs);
        Assert.Contains("cache_layers=" + (resource == "none" ? "" : "current"), outputs);
        Assert.Contains("report_required=false", outputs);
        Assert.Equal(File.ReadAllBytes(fixture.Plan), File.ReadAllBytes(Path.Combine(fixture.Root, "build/ci/plan.json")));
    }

    [Theory]
    [InlineData("keys")]
    [InlineData("restore")]
    [InlineData("snapshot")]
    public void NoResourceCacheEntryNeedsNoSdkToolchainOrCacheConfiguration(string command)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var environment = EnvironmentFor(fixture);
        environment["CANDIDATE_SHA"] = fixture.Commit;
        environment["GITHUB_RUN_ID"] = "";
        environment["GITHUB_RUN_ATTEMPT"] = "";
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(fixture.Root, "build/adapter-bin/python3"),
            ["-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), command,
                "--repository", fixture.Root, "--stage", "current"], environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Empty(result.Text);
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, "build/lean-cache")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/adapter-output")));
    }

    [Theory]
    [InlineData(true, true, true)]
    [InlineData(false, true, false)]
    [InlineData(true, false, true)]
    [InlineData(false, false, true)]
    public void ReportSeedCannotRemoveRegisteredInspectorBuildResources(bool compileInspector, bool seedAvailable, bool needsLake)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["lean-report"]);
        var environment = EnvironmentFor(fixture);
        environment["CANDIDATE_SHA"] = fixture.Commit;
        environment["GITHUB_ENV"] = Path.Combine(fixture.Root, "build/adapter-environment");
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(environment["PATH"], "python3"),
            ["-B", "-c", """
            import json, pathlib, sys
            from unittest.mock import patch
            source = pathlib.Path(sys.argv[1])
            root = pathlib.Path.cwd()
            sys.path.insert(0, str(source / 'tools/scripts/worktree'))
            sys.path.insert(0, str(source / 'tools/scripts/workflow'))
            import lean_actions, ci_plan
            targets = ['LeanInformationAudit', 'leanInspector/reportInspector'] if json.loads(sys.argv[2]) else []
            report = str(root / 'optional-seed/raw-lean-report.json') if json.loads(sys.argv[3]) else None
            # Planning and report acceptance have independent behavioral tests.
            # Exercise the real CLI's resource decision after those boundaries.
            plan = {'execution': {'steps': ['lean-report'], 'lean_targets': targets}}
            requirements = {'required': True, 'tools': ['lake'],
                'cache_layers': ['dependency', 'elan', 'project']}
            with patch.object(sys, 'argv', ['lean_actions.py', 'prepare-report', '--repository', str(root), '--stage', 'current']), \
                    patch.object(ci_plan, 'validate_plan', return_value=plan), \
                    patch.object(ci_plan, 'stage_requirements', return_value=requirements), \
                    patch.object(lean_actions.shutil, 'which', return_value='/fixture/lake'), \
                    patch.object(lean_actions, 'report_seed', return_value=report) as probe:
                code = lean_actions.main()
                probe.assert_called_once_with(root, pathlib.Path('/fixture/lake'))
            raise SystemExit(code)
            """, TestRepositoryLayout.FindRoot(), compileInspector ? "true" : "false", seedAvailable ? "true" : "false"],
            environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(new[] { "needs_lake=" + (needsLake ? "true" : "false") },
            File.ReadAllLines(environment["GITHUB_OUTPUT"]));
        Assert.Equal(new[] { "STRATALINT_LEAN_REPORT_REUSE=" + (seedAvailable
            ? Path.Combine(fixture.Root, "optional-seed/raw-lean-report.json") : "") },
            File.ReadAllLines(environment["GITHUB_ENV"]));
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));
    }

    [Theory]
    [InlineData("current")]
    [InlineData("lean")]
    public void SelectedLeanWorkRequestsDeclaredNativeBuildSeeds(string resource)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([resource]);
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        fixture.Write("lean-toolchain", "leanprover/lean4:v4.22.0\n");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        map = string.Join('\n', map.Split('\n').Select(line => line.Contains("id = \"lean\"", StringComparison.Ordinal)
            ? line.Replace("cache_layers = [], cache_activation = {}", "cache_layers = [\"dependency\", \"elan\", \"project\"], cache_activation = {dependency = \"stage-start\", elan = \"stage-start\", project = \"stage-start\"}", StringComparison.Ordinal)
            : line));
        map += "\n[[files]]\npattern = \"Meta/ci-cache-paths.json\"\nrequire = []\nkind = \"data\"\nadmission_plane = \"judge\"\n"
            + "produced_by = \"none\"\nconsumed_by = [\"test\"]\nverified_by = [\"test\"]\nartifact_id = \"none\"\nruntime_disposition = \"committed-source\"\n";
        fixture.Write("Meta/FILEMAP.toml", map);
        fixture.Write("Meta/ci-cache-paths.json", File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "Meta/ci-cache-paths.json")));
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        environment["CANDIDATE_SHA"] = fixture.Commit;
        environment["GITHUB_RUN_ID"] = "11";
        environment["GITHUB_RUN_ATTEMPT"] = "2";
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(fixture.Root, "build/adapter-bin/python3"),
            ["-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), "keys",
                "--repository", fixture.Root, "--stage", "current"], environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        foreach (var layer in new[] { "dependency", "project", "elan" })
            Assert.Contains(layer + "_key=", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("report_key=", result.Text, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));
    }

    [Theory]
    [InlineData("none", false)]
    [InlineData("lean", true)]
    [InlineData("current", true)]
    public void StageRoutingDeclaresLeanToolchainWithoutMaterializingIt(string resource, bool build)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(resource == "none" ? [] : [resource]);
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Select(line =>
            line.Contains("id = \"lean\"", StringComparison.Ordinal)
                ? line.Replace("tools = []", "tools = [\"lake\"]", StringComparison.Ordinal) : line)));
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        environment["CI_PLAN_PATH"] = "";
        environment["CI_CHANGES_PATH"] = "";
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(fixture.Root, "build/adapter-bin/python3"),
            ["-B", "tools/scripts/workflow/ci.py", "stage-input", "--repository", fixture.Root,
                "--commit", fixture.Commit, "--stage", "current", "--plan", fixture.Plan, "--changes", fixture.Changes], environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(build, JsonNode.Parse(result.Text)!["lake"]!.GetValue<bool>());
        Assert.False(Directory.Exists(Path.Combine(fixture.Root, ".lake")));
    }

    [Fact]
    public void PartialRouteCacheKeysContainOnlyItsDeclaredSeedLayer()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", map.Replace("cache_layers = [], cache_activation = {}", "cache_layers = [\"current\"], cache_activation = {current = \"stage-start\"}", StringComparison.Ordinal));
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        environment["CANDIDATE_SHA"] = fixture.Commit;
        environment["GITHUB_RUN_ID"] = "11";
        environment["GITHUB_RUN_ATTEMPT"] = "2";
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(fixture.Root, "build/adapter-bin/python3"),
            ["-B", Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/worktree/lean_actions.py"), "keys",
                "--repository", fixture.Root, "--stage", "current"], environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("current_key=lean-current-seed-v1-0123456789012345678901234567890123456789-", result.Text, StringComparison.Ordinal);
        foreach (var layer in new[] { "dependency", "project", "report", "judge", "engineering", "elan" })
            Assert.DoesNotContain(layer + "_key=", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("plan")]
    [InlineData("scope")]
    public void BadSelectedPlanCannotStartBootstrap(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        File.WriteAllText(defect == "plan" ? fixture.Plan : fixture.Changes, "[]");
        var result = Shell(fixture, ["build"], EnvironmentFor(fixture));
        Assert.Equal(2, result.Exit);
        Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("dotnet_producer", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void DownloadedShellSelectionReachesNativeRunnerAndPreservesSelectedFailure()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var environment = EnvironmentFor(fixture);
        MaterializePlan(fixture, environment);
        fixture.Write("tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll", "fixture");
        var dotnet = Path.Combine(environment["PATH"], "dotnet");
        File.WriteAllText(dotnet, "#!/bin/bash\nprintf '%s\\n' \"$@\" > build/native-arguments\nexit 1\n");
        SharedBuildContractTests.Process(fixture.Root, "/bin/chmod", ["+x", dotnet]);
        var result = Shell(fixture, ["current"], environment);
        Assert.True(result.Exit == 1, result.Text);
        var arguments = File.ReadAllLines(Path.Combine(fixture.Root, "build/native-arguments"));
        Assert.Contains("--plan", arguments);
        Assert.Contains(Path.Combine(fixture.Root, "build/ci/plan.json"), arguments);
        Assert.Contains("--changes", arguments);
        Assert.Contains(Path.Combine(fixture.Root, "build/ci/changes.json"), arguments);
    }

    [Theory]
    [InlineData("none", 0)]
    [InlineData("TERM", 2)]
    [InlineData("HUP", 2)]
    [InlineData("INT", 2)]
    public void CurrentShellPreservesWrapperCancellationWhenTheChildSucceeds(string signal, int expected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var environment = EnvironmentFor(fixture);
        MaterializePlan(fixture, environment);
        fixture.Write("tools/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll", "fixture");
        foreach (var path in new[] { "tools/scripts/ci-stage.sh", "tools/scripts/lib/resource-observation-lib.sh" })
            fixture.Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
        var dotnet = Path.Combine(environment["PATH"], "dotnet");
        File.WriteAllText(dotnet, "#!/bin/bash\nprintf 'CURRENT_CHILD_STARTED\\n'\nread -r release\nprintf 'CURRENT_CHILD_FINISHED\\n'\n");
        File.SetUnixFileMode(dotnet, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var result = SharedBuildContractTests.Process(fixture.Root, Path.Combine(environment["PATH"], "python3"),
            ["-c", """
            import json, os, signal, subprocess, sys
            child = subprocess.Popen(['/bin/bash', 'tools/scripts/ci-stage.sh', 'current'],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, start_new_session=True)
            output = []
            try:
                for line in child.stdout:
                    output.append(line)
                    if 'CURRENT_CHILD_STARTED' in line:
                        break
                assert any('CURRENT_CHILD_STARTED' in line for line in output), output
                if sys.argv[1] != 'none':
                    os.kill(child.pid, getattr(signal, 'SIG' + sys.argv[1]))
                stdout, stderr = child.communicate('release\n')
                text = ''.join(output) + stdout
                print(json.dumps({'signal': sys.argv[1], 'exit': child.returncode, 'stdout': text, 'stderr': stderr}))
                assert text.count('CURRENT_CHILD_STARTED') == 1, text
                assert text.count('CURRENT_CHILD_FINISHED') == 1, text
                assert child.returncode == int(sys.argv[2]), (child.returncode, text, stderr)
                assert 'CI_STAGE_RESULT stage=current exit=' + sys.argv[2] in text, text
            finally:
                try:
                    os.killpg(child.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                if child.poll() is None:
                    child.wait()
            """, signal, expected.ToString(System.Globalization.CultureInfo.InvariantCulture)],
            environment, TestBudgets.WorkflowProcessHangGuard);
        Assert.True(result.Exit == 0, result.Text);
    }

    [Fact]
    public void ShellRejectsMismatchedFixedCandidateBeforeNoWork()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var environment = EnvironmentFor(fixture);
        environment["CANDIDATE_SHA"] = new string('a', 40);
        var result = Shell(fixture, ["current"], environment);
        Assert.Equal(2, result.Exit);
        Assert.Contains("fixed candidate", result.Text, StringComparison.Ordinal);
    }

    [Fact]
    public void NativePushResolvesOrdinaryDocumentationChangeBeforeSetup()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        fixture.Write("fixtures/selected.txt", "documentation change\n");
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        environment["CI_PLAN_PATH"] = "build/ci/absent-plan.json";
        environment["CI_CHANGES_PATH"] = "build/ci/absent-changes.json";
        SetPushEvent(fixture, environment, SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD^1"));
        var result = Route(fixture, "build", environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal("not-required", Summary(fixture, "build")["status"]!.ToString());
    }

    private static JsonNode Summary(ResourceRouteTests.ResourceFixture fixture, string stage) =>
        JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/" + stage + "-result.json")))!;
    private static void MaterializePlan(ResourceRouteTests.ResourceFixture fixture, Dictionary<string, string> environment)
    {
        var directory = Path.Combine(fixture.Root, "build/ci");
        Directory.CreateDirectory(directory);
        foreach (var name in new[] { "plan", "changes" })
        {
            var path = Path.Combine(directory, name + ".json");
            File.Copy(name == "plan" ? fixture.Plan : fixture.Changes, path, true);
            environment[name == "plan" ? "CI_PLAN_PATH" : "CI_CHANGES_PATH"] = path;
        }
    }

    private static Dictionary<string, string> EnvironmentFor(ResourceRouteTests.ResourceFixture fixture)
    {
        var bin = Path.Combine(fixture.Root, "build/adapter-bin");
        Directory.CreateDirectory(bin);
        foreach (var tool in new[] { "bash", "git", "python3", "dirname", "mkdir", "date", "cat", "rm" })
        {
            var found = SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["-c", "command -v " + tool]);
            Assert.True(found.Exit == 0, found.Text);
            if (!File.Exists(Path.Combine(bin, tool))) File.CreateSymbolicLink(Path.Combine(bin, tool), found.Text.Trim());
        }
        return new() { ["PATH"] = bin, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["GITHUB_EVENT_NAME"] = "", ["GITHUB_EVENT_PATH"] = "",
            ["CI_NEEDS"] = "{}", ["CI_WORKFLOW_INPUTS"] = "null",
            ["CANDIDATE_SHA"] = "",
            ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/adapter-output") };
    }

    private static (int Exit, string Text) Shell(ResourceRouteTests.ResourceFixture fixture, string[] arguments,
        Dictionary<string, string> environment)
    {
        foreach (var path in new[] { "tools/scripts/ci-stage.sh", "tools/scripts/lib/resource-observation-lib.sh" })
            fixture.Write(path, File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), path)));
        return SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["tools/scripts/ci-stage.sh", .. arguments],
            environment, TestBudgets.WorkflowProcessHangGuard);
    }

    private static (int Exit, string Text) Route(ResourceRouteTests.ResourceFixture fixture, string stage,
        Dictionary<string, string> environment) => SharedBuildContractTests.Process(fixture.Root,
            Path.Combine(fixture.Root, "build/adapter-bin/python3"), ["-B", "tools/scripts/workflow/ci.py", "stage-input",
                "--repository", fixture.Root, "--commit", fixture.Commit, "--stage", stage], environment,
            TestBudgets.WorkflowProcessHangGuard);
}
