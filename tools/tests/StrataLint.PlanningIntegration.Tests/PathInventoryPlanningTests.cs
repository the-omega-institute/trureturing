using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.PlanningIntegration.Tests;

[Collection("StrataLint.PlanningIntegration.Tests process boundary")]
public sealed class PathInventoryPlanningTests
{
    [Theory]
    [InlineData("body", false)]
    [InlineData("add", true)]
    [InlineData("delete", true)]
    [InlineData("rename", true)]
    [InlineData("mode", true)]
    [InlineData("index-mode", true)]
    [InlineData("untrack", true)]
    [InlineData("ignored", false)]
    public void ColdLocalPlanSeparatesInventoryFromOrdinaryBodies(string mutation, bool selected)
    {
        if (OperatingSystem.IsWindows() && mutation is "mode" or "index-mode") return;
        using var fixture = InventoryFixture();
        var baseline = fixture.Commit;
        Mutate(fixture, mutation);
        var result = LocalPlan(fixture, baseline);
        Assert.True(result.Exit == 0, result.Text);
        AssertSelection(fixture, selected);
        if (mutation is "index-mode" or "untrack")
        {
            var changes = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/changes.json")))!;
            Assert.Empty(changes["changes"]!.AsArray());
            var metadata = Assert.Single(changes["origin"]!["inventory_changes"]!.AsArray());
            Assert.Equal("fixtures/selected.txt", metadata!["path"]!.ToString());
            Assert.Equal("100644", metadata["old"]!["index_mode"]!.ToString());
            Assert.Equal("100644", metadata["new"]!["effective_mode"]!.ToString());
            if (mutation == "untrack") Assert.Null(metadata["new"]!["index_mode"]);
            else Assert.Equal("100755", metadata["new"]!["index_mode"]!.ToString());
        }
    }

    [Theory]
    [InlineData("push", "body", false)]
    [InlineData("pr", "body", false)]
    [InlineData("push", "add", true)]
    [InlineData("pr", "add", true)]
    [InlineData("push", "delete", true)]
    [InlineData("pr", "delete", true)]
    [InlineData("push", "rename", true)]
    [InlineData("pr", "rename", true)]
    [InlineData("push", "mode", true)]
    [InlineData("pr", "mode", true)]
    public void ImmutablePushAndPrUseStructuralEndpoints(string mode, string mutation, bool selected)
    {
        if (OperatingSystem.IsWindows() && mutation == "mode") return;
        using var fixture = InventoryFixture();
        var baseline = fixture.Commit;
        Mutate(fixture, mutation);
        var result = ImmutablePlan(fixture, baseline, mode);
        Assert.True(result.Exit == 0, result.Text);
        AssertSelection(fixture, selected);
    }

    [Fact]
    public void LocalIndexMutationInvalidatesPreviouslyPreparedPlan()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = InventoryFixture();
        var result = LocalPlan(fixture, fixture.Commit);
        Assert.True(result.Exit == 0, result.Text);
        Mutate(fixture, "index-mode");
        var stale = EngineeringProcess.Process(fixture.Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "validate-plan",
            "--repository", fixture.Root, "--commit", fixture.Commit,
            "--changes", "build/ci/changes.json", "--plan", "build/ci/plan.json"]);
        Assert.Equal(2, stale.Exit);
        Assert.Contains("origin", stale.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("project")]
    [InlineData("resource")]
    [InlineData("non-ci")]
    [InlineData("empty-binding")]
    public void UnselectedInventoryDeclarationsStillRequireExactProjectMapping(string defect)
    {
        using var fixture = InventoryFixture();
        if (defect is "project" or "non-ci")
        {
            var registry = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
            var row = registry["projects"]!.AsArray().Single(p => p!["path"]!.ToString() == ResourceFixture.Foo)!;
            if (defect == "project") row["execution_path_inventory"] = new JsonArray("other/**");
            else row["ci"] = false;
            fixture.Write(EngineeringRegistrationFixture.Path, registry.ToJsonString());
        }
        else if (defect == "resource")
            fixture.Write("Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"))
                .Replace("path_inventory = [\"fixtures/**\"]", "path_inventory = [\"other/**\"]", StringComparison.Ordinal));
        else
        {
            var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "Meta/ci-resources.json")))!;
            mapping["resources"]!.AsArray().Single(row => row!["id"]!.ToString() == "inventory")!["projects"] = new JsonArray();
            fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
        }
        var result = LocalPlan(fixture, fixture.Commit);
        Assert.Equal(2, result.Exit);
        Assert.Contains("inventory", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("target-body", false)]
    [InlineData("retarget", true)]
    [InlineData("to-link", true)]
    [InlineData("from-link", true)]
    public void LinkMetadataChangesSelectInventoryButTargetBodiesDoNot(string mutation, bool selected)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = InventoryFixture();
        fixture.Write("fixtures/other.txt", "other\n");
        var alias = Path.Combine(fixture.Root, "fixtures/alias");
        if (mutation == "to-link") fixture.Write("fixtures/alias", "regular\n");
        else File.CreateSymbolicLink(alias, "selected.txt");
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        var start = map.IndexOf("[[files]]", StringComparison.Ordinal);
        var entry = map[start..];
        var patterns = new[] { ".gitignore", "Meta/**", "fixtures/*.txt", "fixtures/alias", "global.json", "tools/**" };
        var rows = string.Concat(patterns.Select(pattern => entry.Replace("pattern = \"**\"", "pattern = \"" + pattern + "\"", StringComparison.Ordinal)
            + (pattern == "fixtures/alias" && mutation != "to-link" ? "symlink = { target = \"selected.txt\", kind = \"file\" }\n" : "")));
        fixture.Write("Meta/FILEMAP.toml", map[..start] + rows);
        fixture.CommitPlan();
        if (mutation == "target-body") fixture.Write("fixtures/selected.txt", "different ordinary body\n");
        else
        {
            File.Delete(alias);
            if (mutation == "from-link") fixture.Write("fixtures/alias", "regular\n");
            else File.CreateSymbolicLink(alias, mutation == "retarget" ? "other.txt" : "selected.txt");
            var changedMap = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
            const string declaration = "symlink = { target = \"selected.txt\", kind = \"file\" }\n";
            if (mutation == "retarget") changedMap = changedMap.Replace(declaration, declaration.Replace("selected.txt", "other.txt", StringComparison.Ordinal), StringComparison.Ordinal);
            else if (mutation == "from-link") changedMap = changedMap.Replace(declaration, "", StringComparison.Ordinal);
            else changedMap = changedMap.Replace("[[files]]\npattern = \"global.json\"", declaration + "[[files]]\npattern = \"global.json\"", StringComparison.Ordinal);
            fixture.Write("Meta/FILEMAP.toml", changedMap);
        }
        var result = LocalPlan(fixture, fixture.Commit);
        Assert.True(result.Exit == 0, result.Text);
        AssertSelection(fixture, selected);
    }

    [Theory]
    [InlineData("directory")]
    [InlineData("index-type")]
    public void InvalidEffectiveOrIndexEntryTypeFailsClosed(string defect)
    {
        using var fixture = InventoryFixture();
        if (defect == "directory")
        {
            var path = Path.Combine(fixture.Root, "fixtures/selected.txt");
            File.Delete(path);
            Directory.CreateDirectory(path);
        }
        else EngineeringProcess.Git(fixture.Root, "update-index", "--cacheinfo", "160000," + fixture.Commit + ",fixtures/selected.txt");
        var result = LocalPlan(fixture, fixture.Commit);
        Assert.Equal(2, result.Exit);
        Assert.Contains("non-regular", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("body", true)]
    [InlineData("add", true)]
    [InlineData("delete", true)]
    [InlineData("rename", true)]
    [InlineData("mode", true)]
    [InlineData("index-mode", false)]
    [InlineData("untrack", false)]
    [InlineData("unrelated", false)]
    public void ExplicitBodyTriggersSelectOnlyMatchingOrdinaryChanges(string mutation, bool selected)
    {
        if (OperatingSystem.IsWindows() && mutation is "mode" or "index-mode") return;
        using var fixture = InventoryFixture("path_inputs");
        var baseline = fixture.Commit;
        if (mutation == "unrelated") fixture.Write("fixtures/notes.md", "new documentation\n");
        else Mutate(fixture, mutation);
        var result = LocalPlan(fixture, baseline);
        Assert.True(result.Exit == 0, result.Text);
        AssertSelection(fixture, selected, "path_input_require");
    }

    [Theory]
    [InlineData("path_inventory", "delete", "local")]
    [InlineData("path_inputs", "delete", "local")]
    [InlineData("path_inventory", "rename", "local")]
    [InlineData("path_inputs", "rename", "local")]
    [InlineData("path_inventory", "delete", "push")]
    [InlineData("path_inputs", "delete", "push")]
    [InlineData("path_inventory", "rename", "pr")]
    [InlineData("path_inputs", "rename", "pr")]
    public void RemovedAndRenamedOldEndpointsKeepTheirHistoricalResourceTriggers(string field, string mutation, string mode)
    {
        using var fixture = InventoryFixture(field);
        var baseline = fixture.Commit;
        ReplaceTrigger(fixture, field, "other/**");
        Mutate(fixture, mutation);
        var result = mode == "local" ? LocalPlan(fixture, baseline) : ImmutablePlan(fixture, baseline, mode);
        Assert.True(result.Exit == 0, result.Text);
        AssertSelection(fixture, true, field == "path_inventory" ? "inventory_require" : "path_input_require");
        var plan = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/plan.json")))!;
        var old = Assert.Single(plan["paths"]!.AsArray(), row => row!["path"]!.ToString() == "fixtures/selected.txt");
        Assert.Contains(old![field == "path_inventory" ? "inventory_require" : "path_input_require"]!.AsArray(),
            value => value!.ToString() == "inventory");
    }

    [Theory]
    [InlineData("path_inventory", "delete", false)]
    [InlineData("path_inputs", "delete", false)]
    [InlineData("path_inventory", "rename", true)]
    [InlineData("path_inputs", "rename", true)]
    public void CandidateResourceTriggersApplyOnlyToSurvivingOrNewEndpoints(string field, string mutation, bool selected)
    {
        using var fixture = InventoryFixture(field);
        ReplaceTrigger(fixture, field, "other/**");
        fixture.CommitPlan();
        var baseline = fixture.Commit;
        ReplaceTrigger(fixture, field, field == "path_inventory" ? "fixtures/**" : "fixtures/*.txt");
        Mutate(fixture, mutation);
        var result = LocalPlan(fixture, baseline);
        Assert.True(result.Exit == 0, result.Text);
        AssertSelection(fixture, selected, field == "path_inventory" ? "inventory_require" : "path_input_require");
    }

    [Theory]
    [InlineData("path_inventory")]
    [InlineData("path_inputs")]
    public void HistoricalTriggerWithoutCandidateResourceFailsClosed(string field)
    {
        using var fixture = InventoryFixture(field);
        var baseline = fixture.Commit;
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", string.Join('\n', map.Split('\n').Where(line => !line.Contains("{ id = \"inventory\"", StringComparison.Ordinal))));
        var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "Meta/ci-resources.json")))!;
        var rows = mapping["resources"]!.AsArray();
        rows.Remove(rows.Single(row => row!["id"]!.ToString() == "inventory"));
        fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
        if (field == "path_inventory") SetProjectInventory(fixture, new JsonArray());
        Mutate(fixture, "delete");
        var result = LocalPlan(fixture, baseline);
        Assert.Equal(2, result.Exit);
        Assert.Contains("inventory", result.Text, StringComparison.Ordinal);
        Assert.Contains("selected endpoint requirements", result.Text, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("non-ci")]
    [InlineData("empty-binding")]
    public void UnselectedBodyTriggersRequireCompleteCiTestMappings(string defect)
    {
        using var fixture = InventoryFixture("path_inputs");
        if (defect == "non-ci")
        {
            var registry = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
            registry["projects"]!.AsArray().Single(row => row!["path"]!.ToString() == ResourceFixture.Foo)!["ci"] = false;
            fixture.Write(EngineeringRegistrationFixture.Path, registry.ToJsonString());
        }
        else
        {
            var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "Meta/ci-resources.json")))!;
            mapping["resources"]!.AsArray().Single(row => row!["id"]!.ToString() == "inventory")!["projects"] = new JsonArray();
            fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
        }
        var result = LocalPlan(fixture, fixture.Commit);
        Assert.Equal(2, result.Exit);
        Assert.Contains("path_inputs", result.Text, StringComparison.Ordinal);
    }

    private static ResourceFixture InventoryFixture(string field = "path_inventory")
    {
        var fixture = new ResourceFixture([]);
        var registry = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
        var project = registry["projects"]!.AsArray().Single(row => row!["path"]!.ToString() == ResourceFixture.Foo)!;
        project["role"] = "cross-cutting-test";
        project["ci"] = true;
        project["test_partition"] = "inventory-fixture";
        foreach (var executionField in new[] { "execution_inputs", "execution_excludes", "execution_environment", "execution_filemap_paths" })
            project[executionField] = new JsonArray();
        project["execution_path_inventory"] = field == "path_inventory" ? new JsonArray("fixtures/**") : new JsonArray();
        project["references"] = new JsonArray(ResourceFixture.Bar);
        fixture.Write(EngineeringRegistrationFixture.Path, registry.ToJsonString());
        var mapping = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "Meta/ci-resources.json")))!;
        mapping["resources"]!.AsArray().Add(new JsonObject { ["id"] = "inventory", ["projects"] = new JsonArray(ResourceFixture.Foo),
            ["checks"] = new JsonArray(), ["steps"] = new JsonArray() });
        fixture.Write("Meta/ci-resources.json", mapping.ToJsonString());
        const string resource = "  { id = \"inventory\", stage = \"engineering\", owner = \"tools/scripts/workflow/ci.py\", prerequisites = [\"build\"], tools = [], cache_layers = [], cache_activation = {}, materials = [\"Meta/ci-checks.json\", \"Meta/ci-resources.json\", \"Meta/engineering-projects.json\"], path_inventory = [\"fixtures/**\"] },\n";
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        var declaration = field == "path_inventory" ? resource
            : resource.Replace("path_inventory = [\"fixtures/**\"]", "path_inputs = [\"fixtures/*.txt\"]", StringComparison.Ordinal);
        fixture.Write("Meta/FILEMAP.toml", map.Replace("  { id = \"lean\"", declaration + "  { id = \"lean\"", StringComparison.Ordinal));
        fixture.CommitPlan();
        return fixture;
    }

    private static void Mutate(ResourceFixture fixture, string mutation)
    {
        var file = Path.Combine(fixture.Root, "fixtures/selected.txt");
        switch (mutation)
        {
            case "body": fixture.Write("fixtures/selected.txt", "different bytes\n"); break;
            case "add": fixture.Write("fixtures/added.txt", "new\n"); break;
            case "delete": File.Delete(file); break;
            case "rename": File.Move(file, Path.Combine(fixture.Root, "fixtures/renamed.txt")); break;
            case "mode":
                if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(file, File.GetUnixFileMode(file) | UnixFileMode.UserExecute);
                break;
            case "index-mode": EngineeringProcess.Git(fixture.Root, "update-index", "--chmod=+x", "fixtures/selected.txt"); break;
            case "untrack": EngineeringProcess.Git(fixture.Root, "rm", "--cached", "fixtures/selected.txt"); break;
            case "ignored": fixture.Write("build/ignored.txt", "new\n"); break;
        }
    }

    private static (int Exit, string Text) LocalPlan(ResourceFixture fixture, string before) =>
        EngineeringProcess.Process(fixture.Root, "python3", ["-B", "tools/scripts/workflow/ci.py", "push-plan", "--repository", fixture.Root,
            "--commit", fixture.Commit, "--before", before, "--after", fixture.Commit]);

    private static (int Exit, string Text) ImmutablePlan(ResourceFixture fixture, string baseline, string mode)
    {
        string Git(params string[] args) => EngineeringProcess.Git(fixture.Root, args);
        Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "inventory mutation");
        var head = Git("rev-parse", "HEAD");
        var candidate = mode == "push" ? head : Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid",
            "commit-tree", Git("rev-parse", "HEAD^{tree}"), "-p", baseline, "-p", head, "-m", "inventory merge");
        if (mode == "pr") Git("reset", "--hard", candidate);
        var eventPath = Path.Combine(fixture.Root, "build/inventory-event.json");
        File.WriteAllText(eventPath, JsonSerializer.Serialize(new { before = baseline, after = candidate }));
        return EngineeringProcess.Process(fixture.Root, "python3", ["-B", "tools/scripts/workflow/ci.py", mode + "-plan",
            "--repository", fixture.Root, "--commit", candidate,
            .. mode == "push" ? new[] { "--before", baseline, "--after", candidate } : ["--base", baseline, "--head", head]],
            new Dictionary<string, string> { ["GITHUB_EVENT_NAME"] = mode == "push" ? "push" : "pull_request",
                ["GITHUB_EVENT_PATH"] = eventPath, ["GITHUB_OUTPUT"] = Path.Combine(fixture.Root, "build/inventory-output") });
    }

    private static void ReplaceTrigger(ResourceFixture fixture, string field, string pattern)
    {
        var map = File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"));
        fixture.Write("Meta/FILEMAP.toml", System.Text.RegularExpressions.Regex.Replace(map,
            field + @" = \[[^\]]*\]", field + " = [\"" + pattern + "\"]"));
        if (field == "path_inventory") SetProjectInventory(fixture, new JsonArray(pattern));
    }

    private static void SetProjectInventory(ResourceFixture fixture, JsonArray patterns)
    {
        var registry = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path)))!;
        registry["projects"]!.AsArray().Single(row => row!["path"]!.ToString() == ResourceFixture.Foo)!["execution_path_inventory"] = patterns;
        fixture.Write(EngineeringRegistrationFixture.Path, registry.ToJsonString());
    }

    private static void AssertSelection(ResourceFixture fixture, bool selected, string reason = "inventory_require")
    {
        var plan = JsonNode.Parse(File.ReadAllText(Path.Combine(fixture.Root, "build/ci/plan.json")))!;
        Assert.Equal(selected ? new[] { "build", "inventory" } : [], plan["resources"]!.AsArray().Select(v => v!.ToString()));
        Assert.Equal(selected ? new[] { ResourceFixture.Foo } : [], plan["execution"]!["tests"]!.AsArray().Select(v => v!.ToString()));
        Assert.DoesNotContain(ResourceFixture.Bar, plan["execution"]!["tests"]!.AsArray().Select(v => v!.ToString()));
        if (selected) Assert.Contains(plan["paths"]!.AsArray(), row => row![reason]?.AsArray().Any(v => v!.ToString() == "inventory") == true);
    }
}
