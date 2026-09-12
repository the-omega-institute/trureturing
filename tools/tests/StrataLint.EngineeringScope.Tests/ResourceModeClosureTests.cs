using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ResourceModeClosureTests(Xunit.Abstractions.ITestOutputHelper output)
{
    [Theory]
    [InlineData("push", "delta", "", "", "", "", "")]
    [InlineData("pr", "delta", "build,current,delta,lean,lean-report", "build,current,delta", "dotnet,git,lake", "current,judge,project,report", "lean-report,check-current")]
    [InlineData("push", "current,delta", "build,current,lean,lean-report", "build,current", "dotnet,lake", "current,judge,project,report", "lean-report,check-current")]
    [InlineData("pr", "current,delta", "build,current,delta,lean,lean-report", "build,current,delta", "dotnet,git,lake", "current,judge,project,report", "lean-report,check-current")]
    [InlineData("push", "delta,engineering", "build,engineering", "build,engineering", "dotnet", "engineering,judge", "")]
    [InlineData("pr", "delta,engineering", "build,current,delta,engineering,lean,lean-report", "build,engineering,current,delta", "dotnet,git,lake", "current,engineering,judge,project,report", "lean-report,check-current")]
    [InlineData("push", "current", "build,current,lean,lean-report", "build,current", "dotnet,lake", "current,judge,project,report", "lean-report,check-current")]
    [InlineData("pr", "current", "build,current,lean,lean-report", "build,current", "dotnet,lake", "current,judge,project,report", "lean-report,check-current")]
    [InlineData("push", "engineering", "build,engineering", "build,engineering", "dotnet", "engineering,judge", "")]
    [InlineData("pr", "engineering", "build,engineering", "build,engineering", "dotnet", "engineering,judge", "")]
    [InlineData("push", "", "", "", "", "", "")]
    [InlineData("pr", "", "", "", "", "", "")]
    public void ModeSelectsOnlyApplicableRegisteredRootsAndTheirPrerequisites(string mode, string required,
        string resources, string stages, string tools, string caches, string steps)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        Register(fixture, Split(required));
        var result = Plan(fixture, mode);
        Assert.True(result.Exit == 0, result.Text);
        var plan = ReadPlan(fixture);
        output.WriteLine("RESOURCE_MODE_PLAN " + plan.ToJsonString());
        Assert.Equal(mode, plan["mode"]!.ToString());
        Assert.Equal(Split(required), Strings(plan["declared_require"]!));
        Assert.Equal(Split(resources), Strings(plan["resources"]!));
        Assert.Equal(Split(stages), Strings(plan["selected_stages"]!));
        Assert.Equal(Split(tools), Strings(plan["tools"]!));
        Assert.Equal(Split(caches), Strings(plan["cache_layers"]!));
        Assert.Equal(Split(steps), Strings(plan["execution"]!["steps"]!));
        Assert.Equal(steps.Length == 0 ? [] : new[] { "SL-015" }, Strings(plan["execution"]!["checks"]!));
        if (resources.Length == 0)
        {
            Assert.Empty(Strings(plan["materials"]!));
            Assert.Empty(Strings(plan["execution"]!["projects"]!));
        }
        if (mode == "push")
        {
            Assert.Equal("event-range", plan["origin"]!["kind"]!.ToString());
            Assert.Equal("not-applicable", plan["stages"]!["delta"]!["status"]!.ToString());
            Assert.Null(plan["base"]);
            Assert.Null(plan["head"]);
        }
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void DeltaStageAliasesAndTheirDeltaDependenciesObeyTheSameModeBoundary(string mode)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        Register(fixture, ["delta-followup"], followup: true);
        var result = Plan(fixture, mode);
        Assert.True(result.Exit == 0, result.Text);
        var plan = ReadPlan(fixture);
        Assert.Equal(new[] { "delta-followup" }, Strings(plan["declared_require"]!));
        Assert.Equal(mode == "push" ? [] : new[] { "build", "current", "delta", "delta-followup", "lean", "lean-report" }, Strings(plan["resources"]!));
        Assert.Equal(mode == "push" ? [] : new[] { "build", "current", "delta" }, Strings(plan["selected_stages"]!));
        if (mode == "push")
        {
            Assert.Empty(Strings(plan["tools"]!));
            Assert.Empty(Strings(plan["cache_layers"]!));
            Assert.Empty(Strings(plan["execution"]!["steps"]!));
        }
    }

    [Theory]
    [InlineData("push", "build")]
    [InlineData("push", "engineering")]
    [InlineData("push", "current")]
    [InlineData("pr", "build")]
    [InlineData("pr", "engineering")]
    [InlineData("pr", "current")]
    public void NonDeltaResourcesCannotDependOnDeltaEvenWhenUnselected(string mode, string resource)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        Register(fixture, [], invalidDependency: resource);
        var result = Plan(fixture, mode);
        Assert.Equal(2, result.Exit);
        Assert.Contains("conflicting resource stage dependency: " + resource + " -> delta", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/plan.json")));
    }

    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void UnselectedDeltaCyclesStillFailRegistration(string mode)
    {
        using var fixture = new ResourceRouteTests.ResourceFixture([]);
        Register(fixture, [], invalidDependency: "delta");
        var result = Plan(fixture, mode);
        Assert.Equal(2, result.Exit);
        Assert.Contains("cyclic resource: delta", result.Text, StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/plan.json")));
    }

    private static void Register(ResourceRouteTests.ResourceFixture fixture, string[] required, bool followup = false,
        string? invalidDependency = null)
    {
        const string mappingPath = "Meta/ci-resources.json";
        var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, mappingPath)))!;
        mapping["resources"]!.AsArray().Add(JsonNode.Parse("""{"id":"delta","projects":[],"checks":[],"steps":[]}"""));
        mapping["resources"]!.AsArray().Add(JsonNode.Parse("""{"id":"engineering","projects":["tools/Foo/Foo.csproj"],"checks":[],"steps":[]}"""));
        if (followup) mapping["resources"]!.AsArray().Add(JsonNode.Parse("""{"id":"delta-followup","projects":[],"checks":[],"steps":[]}"""));
        fixture.Write(mappingPath, mapping.ToJsonString());
        var filemap = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        const string materials = "materials = [\"Meta/ci-checks.json\", \"Meta/ci-resources.json\", \"Meta/engineering-projects.json\"]";
        string Row(string id, string stage, string dependency, string tool, string cache) =>
            "  { id = \"" + id + "\", stage = \"" + stage + "\", owner = \"tools/scripts/workflow/ci.py\", prerequisites = [\"" + dependency
            + "\"], tools = [\"" + tool + "\"], cache_layers = " + (cache.Length == 0 ? "[]" : "[\"" + cache + "\"]") + ", " + materials + " },\n";
        var added = Row("delta", "delta", invalidDependency == "delta" ? "delta" : "current", "git", "")
            + (followup ? Row("delta-followup", "delta", "delta", "git", "") : "")
            + Row("engineering", "engineering", invalidDependency == "engineering" ? "delta" : "build", "dotnet", "engineering");
        filemap = filemap.Replace("  { id = \"filemap\"", added + "  { id = \"filemap\"", StringComparison.Ordinal)
            .Replace("require = []", "require = " + JsonSerializer.Serialize(required), StringComparison.Ordinal);
        var rows = filemap.Split('\n');
        foreach (var (id, tool, cache) in new[] { ("build", "dotnet", "judge"), ("current", "dotnet", "current"), ("lean", "lake", "project"), ("lean-report", "lake", "report") })
            for (var i = 0; i < rows.Length; i++)
                if (rows[i].Contains("id = \"" + id + "\"", StringComparison.Ordinal))
                {
                    rows[i] = rows[i].Replace("tools = []", "tools = [\"" + tool + "\"]", StringComparison.Ordinal)
                        .Replace("cache_layers = []", "cache_layers = [\"" + cache + "\"]", StringComparison.Ordinal);
                    if (id == invalidDependency)
                        rows[i] = rows[i].Replace(id == "build" ? "prerequisites = []" : "prerequisites = [\"lean-report\"]",
                            "prerequisites = [\"delta\"]", StringComparison.Ordinal);
                }
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', rows));
    }

    private static (int Exit, string Text) Plan(ResourceRouteTests.ResourceFixture fixture, string mode)
    {
        string Git(params string[] arguments) => SharedBuildContractTests.Git(fixture.Root, arguments);
        void Commit(string message) => Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", message);
        Git("add", "."); Commit("registered resource modes");
        var basis = Git("rev-parse", "HEAD");
        fixture.Write("fixtures/selected.txt", "candidate input\n");
        Git("add", "."); Commit("candidate input");
        var head = Git("rev-parse", "HEAD");
        var candidate = Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit-tree",
            Git("rev-parse", "HEAD^{tree}"), "-p", basis, "-p", head, "-m", "candidate merge");
        Git("reset", "--hard", candidate);
        var eventPath = Path.Combine(fixture.Root, "build/mode-event.json");
        File.WriteAllText(eventPath, JsonSerializer.Serialize(new { before = basis, after = candidate }));
        return SharedBuildContractTests.Process(fixture.Root, "python3", ["-B", "tools/scripts/workflow/ci.py", mode + "-plan",
            "--repository", fixture.Root, "--commit", candidate,
            .. mode == "push" ? new[] { "--before", basis, "--after", candidate } : ["--base", basis, "--head", head]],
            new Dictionary<string, string>
            {
                ["GITHUB_EVENT_NAME"] = mode == "push" ? "push" : "pull_request_target", ["GITHUB_EVENT_PATH"] = eventPath,
                ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/mode-output"),
                ["GITHUB_STEP_SUMMARY"] = Path.Combine(fixture.Root, "build/mode-summary"),
            }, TestBudgets.ScriptProcessHangGuard);
    }

    private static JsonNode ReadPlan(ResourceRouteTests.ResourceFixture fixture) =>
        JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/plan.json")))!;
    private static string[] Split(string value) => value.Split(',', StringSplitOptions.RemoveEmptyEntries);
    private static string[] Strings(JsonNode node) => node.AsArray().Select(value => value!.ToString()).ToArray();
}
