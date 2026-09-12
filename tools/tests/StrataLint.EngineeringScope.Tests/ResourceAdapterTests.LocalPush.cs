using System.Security.Cryptography;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class ResourceAdapterTests
{
    [Theory]
    [InlineData("unstaged")]
    [InlineData("staged")]
    [InlineData("staged-then-unstaged")]
    [InlineData("untracked")]
    [InlineData("delete")]
    [InlineData("rename")]
    public void DirtyPushAfterDocCommitExecutesRegisteredCurrentOnEffectiveInputs(string change)
    {
        using var fixture = LocalFixture();
        const string oldPath = "fixtures/required name\tΩ\n.txt";
        const string newPath = "docs/renamed name\tΩ\n.md";
        fixture.Write(oldPath, "required input\n");
        fixture.CommitPlan();
        DocCommit(fixture);
        if (change == "delete") File.Delete(Path.Combine(fixture.Root, oldPath));
        else if (change == "rename") File.Move(Path.Combine(fixture.Root, oldPath), Path.Combine(fixture.Root, newPath));
        else fixture.Write(change == "untracked" ? "fixtures/untracked.txt" : oldPath, "effective local bytes\n");
        if (change == "staged") SharedBuildContractTests.Git(fixture.Root, "add", oldPath);
        if (change == "staged-then-unstaged")
        {
            SharedBuildContractTests.Git(fixture.Root, "add", oldPath);
            fixture.Write(oldPath, "working bytes override staged bytes\n");
        }
        var state = LocalState(fixture);
        var environment = LocalEnvironment(fixture, required: true);
        var result = LocalPreflight(fixture, environment);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(state, LocalState(fixture));
        var plan = PushSelection(fixture);
        Assert.Equal(new[] { "build", "filemap" }, Strings(plan["resources"]!));
        Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["steps"]!));
        Assert.Null(plan["candidate"]!["tree"]);
        Assert.NotNull(plan["origin"]!["worktree"]);
        var selected = Strings(plan["paths"]!, "path");
        Assert.Contains(change == "untracked" ? "fixtures/untracked.txt" : oldPath, selected);
        if (change == "rename") Assert.Contains(newPath, selected);
        if (change == "staged-then-unstaged")
        {
            var endpoint = PushScope(fixture)["origin"]!["worktree"]!.AsArray()
                .Single(row => row!["new"]?["path"]?.ToString() == oldPath)!["new"]!;
            Assert.Equal(SharedBuildContractTests.Git(fixture.Root, "hash-object", "--", oldPath), endpoint["oid"]!.ToString());
            Assert.NotEqual(SharedBuildContractTests.Git(fixture.Root, "rev-parse", ":" + oldPath), endpoint["oid"]!.ToString());
        }
        Assert.Equal(new[] { "dotnet filemap-conform" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
        var current = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.Equal(CommonExecutionEvidence.Candidate(fixture.Root), current.Candidate);
        Assert.NotEqual(fixture.Commit, current.Candidate);
        var unit = Assert.Single(CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units);
        Assert.Equal("filemap", unit.Id);
        Assert.Equal("executed", unit.Status);
        Assert.Single(unit.Operations);
        RetainLocal(fixture, change, result);
    }

    [Fact]
    public void DirtyFilemapCanRequireProductionCurrentForLocalDocs()
    {
        using var fixture = LocalFixture();
        DocCommit(fixture);
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", map.Replace("pattern = \"docs/*\"\nrequire = []",
            "pattern = \"docs/*\"\nrequire = [\"filemap\"]", StringComparison.Ordinal));
        fixture.Write("docs/note.md", "locally registered required documentation\n");
        var state = LocalState(fixture);
        var result = LocalPreflight(fixture, LocalEnvironment(fixture, required: true));
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(state, LocalState(fixture));
        var plan = PushSelection(fixture);
        Assert.Equal(new[] { "filemap" }, Strings(plan["execution"]!["steps"]!));
        Assert.Null(plan["candidate"]!["tree"]);
        Assert.Equal(new[] { "dotnet filemap-conform" }, File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
        var current = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        Assert.Equal(CommonExecutionEvidence.Candidate(fixture.Root), current.Candidate);
        var unit = Assert.Single(CommonExecutionEvidence.Read<CommonCheckRecord>(fixture.Root, CommonExecutionEvidence.ChecksPath("current")).Units);
        Assert.Equal("filemap", unit.Id);
        Assert.Equal("executed", unit.Status);
        Assert.Single(unit.Operations);
        RetainLocal(fixture, "registration-required-docs", result);
    }

    [Theory]
    [InlineData("unstaged")]
    [InlineData("staged")]
    [InlineData("untracked")]
    public void DirtyDeclaredDocsProduceHonestNoWorkWithoutSdkOrCache(string change)
    {
        using var fixture = LocalFixture();
        DocCommit(fixture);
        fixture.Write(change == "untracked" ? "docs/untracked.md" : "docs/note.md", "local documentation\n");
        if (change == "staged") SharedBuildContractTests.Git(fixture.Root, "add", "docs/note.md");
        var state = LocalState(fixture);
        var result = LocalPreflight(fixture, LocalEnvironment(fixture, required: false));
        Assert.True(result.Exit == 0, result.Text);
        Assert.Equal(state, LocalState(fixture));
        Assert.Null(PushSelection(fixture)["candidate"]!["tree"]);
        Assert.Empty(Strings(PushSelection(fixture)["resources"]!));
        foreach (var stage in new[] { "engineering", "current" })
        {
            var summary = Summary(fixture, stage);
            Assert.Equal("not-required", summary["status"]!.ToString());
            Assert.Empty(summary["steps"]!.AsArray());
            Assert.Empty(summary["artifacts"]!.AsArray());
        }
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/launched")));
        Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.BuildPath)));
        RetainLocal(fixture, "docs-" + change, result);
    }

    [Theory]
    [InlineData("filemap")]
    [InlineData("execution")]
    [InlineData("projects")]
    [InlineData("checks")]
    public void DirtyPushUsesEffectiveRegistrationManifests(string registration)
    {
        using var fixture = LocalFixture();
        if (registration == "projects")
        {
            var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "Meta/ci-resources.json")))!;
            mapping["resources"]!.AsArray().Single(r => r!["id"]!.ToString() == "filemap")!["projects"] =
                new JsonArray(ResourceRouteTests.ResourceFixture.Bar, ResourceRouteTests.ResourceFixture.Foo);
            fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
            fixture.CommitPlan();
        }
        DocCommit(fixture);
        fixture.Write("fixtures/selected.txt", "required local bytes\n");
        if (registration == "filemap")
        {
            var path = Path.Combine(fixture.Root, "Meta/FILEMAP.toml");
            File.WriteAllText(path, File.ReadAllText(path).Replace("require = [\"filemap\"]", "require = [\"lean\"]", StringComparison.Ordinal));
        }
        else
        {
            var path = registration == "execution" ? "Meta/ci-resources.json" : registration == "projects" ? EngineeringRegistrationFixture.Path : CommonExecutionEvidence.CheckManifestPath;
            var data = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, path)))!;
            if (registration == "execution") data["resources"]!.AsArray().Single(r => r!["id"]!.ToString() == "filemap")!["projects"] = new JsonArray(ResourceRouteTests.ResourceFixture.Bar);
            if (registration == "projects") data["projects"]!.AsArray().Single(r => r!["path"]!.ToString() == ResourceRouteTests.ResourceFixture.Foo)!["references"] = new JsonArray(ResourceRouteTests.ResourceFixture.Bar);
            if (registration == "checks") data["checks"]!.AsArray().Single(r => r!["id"]!.ToString() == "filemap")!["report_inputs"] = new JsonArray(new JsonObject { ["artifact"] = "required-report" });
            fixture.Write(path, data.ToJsonString());
        }
        var state = LocalState(fixture);
        var result = PushPlan(fixture);
        Assert.Equal(state, LocalState(fixture));
        if (registration == "checks")
        {
            Assert.Equal(2, result.Exit);
            Assert.Contains("selected check requires lean-report: filemap", result.Text, StringComparison.Ordinal);
        }
        else
        {
            Assert.True(result.Exit == 0, result.Text);
            var plan = PushSelection(fixture);
            Assert.Null(plan["candidate"]!["tree"]);
            if (registration == "filemap") Assert.Equal(new[] { "lean" }, Strings(plan["execution"]!["steps"]!));
            if (registration == "execution") Assert.Equal(new[] { ResourceRouteTests.ResourceFixture.Bar }, Strings(plan["execution"]!["projects"]!));
            if (registration == "projects") Assert.Equal(new[] { ResourceRouteTests.ResourceFixture.Foo }, Strings(plan["execution"]!["projects"]!));
        }
        RetainLocal(fixture, "registration-" + registration, result);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void DirtyRegistrationFailureNamesUnregisteredOrConflictingPath(bool conflict)
    {
        using var fixture = LocalFixture();
        DocCommit(fixture);
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        if (conflict)
        {
            var start = map.IndexOf("[[files]]\npattern = \"fixtures/*\"", StringComparison.Ordinal);
            var end = map.IndexOf("[[files]]", start + 1, StringComparison.Ordinal);
            var overlap = map[start..end].Replace("fixtures/*", "fixtures/s*", StringComparison.Ordinal);
            fixture.Write("Meta/FILEMAP.toml", map.Insert(end, overlap));
        }
        fixture.Write(conflict ? "fixtures/selected.txt" : "missing/unregistered.md", "no inferred ownership\n");
        var result = LocalPreflight(fixture, LocalEnvironment(fixture, required: false));
        Assert.Equal(2, result.Exit);
        // The changed endpoint and both matching patterns must remain visible.
        Assert.Contains(conflict ? "fixtures/selected.txt: FILEMAP match count 2" : "missing/unregistered.md: FILEMAP match count 0", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/launched")));
        RetainLocal(fixture, "invalid-registration-" + conflict, result);
    }

    [Theory]
    [InlineData("bytes")]
    [InlineData("scope")]
    [InlineData("material")]
    [InlineData("registration")]
    public void DirtyPushRejectsStaleScopeAndDownstreamMaterial(string defect)
    {
        using var fixture = LocalFixture();
        DocCommit(fixture);
        fixture.Write("fixtures/selected.txt", "local input one\n");
        var environment = LocalEnvironment(fixture, required: true);
        var result = LocalPreflight(fixture, environment);
        Assert.True(result.Exit == 0, result.Text);
        var current = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
        if (defect == "material")
        {
            File.AppendAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.CliPath), "substituted binary");
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateCurrent(fixture.Root));
        }
        else
        {
            if (defect == "bytes") fixture.Write("fixtures/selected.txt", "local input two\n");
            else if (defect == "registration")
            {
                var path = Path.Combine(fixture.Root, "Meta/FILEMAP.toml");
                File.WriteAllText(path, File.ReadAllText(path).Replace("require = [\"filemap\"]", "require = []", StringComparison.Ordinal));
            }
            else
            {
                var scope = PushScope(fixture);
                scope["origin"]!["worktree"] = new JsonArray();
                File.WriteAllText(PushScopePath(fixture), scope.ToJsonString());
                File.WriteAllText(Path.Combine(fixture.Root, current.Selection!.Changes), scope.ToJsonString());
            }
            Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.ValidateCurrent(fixture.Root));
            environment["CI_PLAN_PATH"] = PushPlanPath(fixture);
            environment["CI_CHANGES_PATH"] = PushScopePath(fixture);
            result = Shell(fixture, ["current"], environment);
            Assert.Equal(2, result.Exit);
            Assert.Contains("CI_INPUT_FAILED", result.Text, StringComparison.Ordinal);
        }
        Assert.Single(File.ReadAllLines(Path.Combine(fixture.Root, "build/launched")));
        RetainLocal(fixture, "stale-" + defect, result);
    }

    private static ResourceRouteTests.ResourceFixture LocalFixture()
    {
        var fixture = new ResourceRouteTests.ResourceFixture(["filemap"]);
        ColdPreflightContractTests.Configure(fixture);
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        var index = map.IndexOf("[[files]]", StringComparison.Ordinal);
        var row = map[index..];
        fixture.Write("Meta/FILEMAP.toml", map[..index] + string.Concat(new[] { "*", "Meta/**", "docs/*", "fixtures/*", "tools/**" }.Select(pattern =>
            row.Replace("pattern = \"**\"", "pattern = \"" + pattern + "\"", StringComparison.Ordinal)
               .Replace("require = [\"filemap\"]", pattern == "fixtures/*" ? "require = [\"filemap\"]" : "require = []", StringComparison.Ordinal))));
        var checks = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, CommonExecutionEvidence.CheckManifestPath)))!;
        var check = checks["checks"]!.AsArray().Single(r => r!["id"]!.ToString() == "filemap")!;
        check["materials"] = new JsonArray("fixtures/*");
        check["path_inventory"] = new JsonArray("fixtures/*");
        fixture.Write(CommonExecutionEvidence.CheckManifestPath, checks.ToJsonString());
        fixture.Write("docs/note.md", "original docs\n");
        fixture.CommitPlan();
        // Both no-work and required cases start cold; preflight owns any build.
        File.Delete(Path.Combine(fixture.Root, CommonExecutionEvidence.BuildPath));
        return fixture;
    }

    private static void DocCommit(ResourceRouteTests.ResourceFixture fixture)
    {
        fixture.Write("docs/note.md", "committed documentation only\n");
        fixture.CommitPlan();
        Assert.True(PushPlan(fixture).Exit == 0);
        Assert.Empty(Strings(PushSelection(fixture)["resources"]!));
    }

    private static Dictionary<string, string> LocalEnvironment(ResourceRouteTests.ResourceFixture fixture, bool required)
    {
        var environment = required ? ColdPreflightContractTests.EnvironmentFor(fixture) : EnvironmentFor(fixture);
        environment["MODE"] = "push";
        environment["BASE"] = "not-an-immutable-base";
        environment["CANDIDATE_SHA"] = "";
        environment["GITHUB_EVENT_NAME"] = "";
        environment["CI_PLAN_PATH"] = "";
        environment["CI_CHANGES_PATH"] = "";
        environment["GIT_OPTIONAL_LOCKS"] = "0";
        return environment;
    }

    private static (int Exit, string Text) LocalPreflight(ResourceRouteTests.ResourceFixture fixture, Dictionary<string, string> environment) =>
        SharedBuildContractTests.Process(fixture.Root, "/bin/bash", ["tools/scripts/preflight.sh"], environment, TestBudgets.WorkflowProcessHangGuard);

    private static string LocalState(ResourceRouteTests.ResourceFixture fixture)
    {
        var paths = SharedBuildContractTests.Git(fixture.Root, "ls-files", "--cached", "--others", "--exclude-standard", "-z").Split('\0', StringSplitOptions.RemoveEmptyEntries);
        var state = new JsonObject {
            ["head"] = SharedBuildContractTests.Git(fixture.Root, "rev-parse", "HEAD"),
            ["status"] = SharedBuildContractTests.Git(fixture.Root, "--no-optional-locks", "status", "--porcelain", "--untracked-files=all"),
            ["index"] = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(Path.Combine(fixture.Root, ".git/index")))),
        };
        foreach (var path in paths.Order(StringComparer.Ordinal))
            state[path] = File.Exists(Path.Combine(fixture.Root, path)) ? Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(Path.Combine(fixture.Root, path)))) : null;
        return state.ToJsonString();
    }

    private static void RetainLocal(ResourceRouteTests.ResourceFixture fixture, string scenario, (int Exit, string Text) result)
    {
        if (Environment.GetEnvironmentVariable("LOCAL_PUSH_EVIDENCE") is not { Length: > 0 } evidence) return;
        JsonNode? Read(string path) => File.Exists(Path.Combine(fixture.Root, path)) ? JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, path))) : null;
        File.AppendAllText(evidence, new JsonObject {
            ["scenario"] = scenario, ["exit"] = result.Exit, ["output"] = result.Text,
            ["plan"] = Read("build/ci/plan.json"), ["scope"] = Read("build/ci/changes.json"),
            ["engineering"] = Read("build/ci/engineering-result.json"), ["current"] = Read("build/ci/current-result.json"),
            ["current_evidence"] = Read(CommonExecutionEvidence.CurrentPath), ["checks"] = Read(CommonExecutionEvidence.ChecksPath("current")),
        }.ToJsonString() + "\n");
    }
}
