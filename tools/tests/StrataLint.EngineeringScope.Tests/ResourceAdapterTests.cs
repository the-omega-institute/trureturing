using System.Text;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed partial class ResourceAdapterTests
{
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
    [InlineData("malformed")]
    [InlineData("candidate")]
    [InlineData("prerequisite")]
    public void WorkflowRouteFailsClosedBeforeSetup(string defect)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        var environment = EnvironmentFor(fixture);
        environment.Remove("CI_PLAN_PATH");
        environment.Remove("CI_CHANGES_PATH");
        environment["CI_PLAN_B64"] = Encode(File.ReadAllText(fixture.Plan));
        environment["CI_CHANGES_B64"] = Encode(File.ReadAllText(fixture.Changes));
        if (defect == "missing") environment["CI_PLAN_B64"] = "";
        if (defect == "malformed") environment["CI_PLAN_B64"] = "not base64!";
        if (defect == "candidate")
        {
            var plan = JsonNode.Parse(File.ReadAllText(fixture.Plan))!;
            plan["candidate"]!["commit"] = new string('a', 40);
            environment["CI_PLAN_B64"] = Encode(plan.ToJsonString());
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
        filemap = filemap.Replace("tools = [], cache_layers = []", "tools = [\"dotnet\"], cache_layers = [\"current\"]", StringComparison.Ordinal);
        fixture.Write("Meta/FILEMAP.toml", filemap);
        fixture.CommitPlan();
        var environment = EnvironmentFor(fixture);
        environment.Remove("CI_PLAN_PATH");
        environment.Remove("CI_CHANGES_PATH");
        environment["CI_PLAN_B64"] = Encode(File.ReadAllText(fixture.Plan));
        environment["CI_CHANGES_B64"] = Encode(File.ReadAllText(fixture.Changes));
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

    [Fact]
    public void PartialRouteCacheKeysContainOnlyItsDeclaredSeedLayer()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        fixture.Write("lake-manifest.json", "{\"packages\":[{\"name\":\"mathlib\",\"rev\":\"0123456789012345678901234567890123456789\"}]}");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", map.Replace("cache_layers = []", "cache_layers = [\"current\"]", StringComparison.Ordinal));
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
    public void SerializedShellSelectionReachesNativeRunnerAndPreservesSelectedFailure()
    {
        using var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        var environment = EnvironmentFor(fixture);
        environment.Remove("CI_PLAN_PATH");
        environment.Remove("CI_CHANGES_PATH");
        environment["CI_PLAN_B64"] = Encode(File.ReadAllText(fixture.Plan));
        environment["CI_CHANGES_B64"] = Encode(File.ReadAllText(fixture.Changes));
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
        environment["GITHUB_EVENT_NAME"] = "push";
        var result = Route(fixture, "build", environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal("not-required", Summary(fixture, "build")["status"]!.ToString());
    }

    private static JsonNode Summary(ResourceRouteTests.ResourceFixture fixture, string stage) =>
        JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/" + stage + "-result.json")))!;
    private static string Encode(string text) => Convert.ToBase64String(Encoding.UTF8.GetBytes(text));

    private static Dictionary<string, string> EnvironmentFor(ResourceRouteTests.ResourceFixture fixture)
    {
        var bin = Path.Combine(fixture.Root, "build/adapter-bin");
        Directory.CreateDirectory(bin);
        foreach (var tool in new[] { "bash", "git", "python3", "dirname", "mkdir", "date", "cat", "rm" })
        {
            var found = SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["-c", "command -v " + tool]);
            Assert.True(found.Exit == 0, found.Text);
            File.CreateSymbolicLink(Path.Combine(bin, tool), found.Text.Trim());
        }
        return new() { ["PATH"] = bin, ["CI_PLAN_PATH"] = fixture.Plan, ["CI_CHANGES_PATH"] = fixture.Changes,
            ["CI_PLAN_B64"] = "", ["CI_CHANGES_B64"] = "", ["CI_NEEDS"] = "{}", ["CI_WORKFLOW_INPUTS"] = "null",
            ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/adapter-output") };
    }

    private static (int Exit, string Text) Shell(ResourceRouteTests.ResourceFixture fixture, string[] arguments,
        Dictionary<string, string> environment)
    {
        fixture.Write("tools/scripts/ci-stage.sh", File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/ci-stage.sh")));
        return SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["tools/scripts/ci-stage.sh", .. arguments],
            environment, TestBudgets.WorkflowProcessHangGuard);
    }

    private static (int Exit, string Text) Route(ResourceRouteTests.ResourceFixture fixture, string stage,
        Dictionary<string, string> environment) => SharedBuildContractTests.Process(fixture.Root,
            Path.Combine(fixture.Root, "build/adapter-bin/python3"), ["-B", "tools/scripts/workflow/ci.py", "stage-input",
                "--repository", fixture.Root, "--commit", fixture.Commit, "--stage", stage], environment,
            TestBudgets.WorkflowProcessHangGuard);
}
