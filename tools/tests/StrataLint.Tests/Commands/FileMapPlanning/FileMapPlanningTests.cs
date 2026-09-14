using StrataLint.Cli;
using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed class FileMapPlanningTests
{
    [Fact]
    public void ReferenceOnlyParentlessCurrentReturnsHonestNoWorkWithoutToolsOrBase()
    {
        using var fixture = new FileMapPlanningFixture();
        var changes = fixture.Changes();
        changes["change_count"] = 1;
        changes["changes"]!.AsArray().Add(new JsonObject { ["status"] = "A", ["old"] = null,
            ["new"] = fixture.Endpoint("README.md") });
        fixture.Supply(changes);
        var planned = fixture.MakePlan();
        Assert.True(planned.ExitCode == 0, FileMapPlanningFixture.Text(planned));
        var plan = FileMapPlanningFixture.Read(fixture.Plan);
        Assert.Empty(plan["resources"]!.AsArray());
        Assert.Empty(plan["tools"]!.AsArray());
        Assert.Empty(plan["cache_layers"]!.AsArray());
        Assert.Equal("README.md", plan["paths"]![0]!["path"]!.GetValue<string>());
        Assert.Equal(0, fixture.NoWork().ExitCode);
        var result = FileMapPlanningFixture.Read(fixture.Result);
        Assert.Equal("not-required", result["status"]!.GetValue<string>());
        Assert.True(JsonNode.DeepEquals(changes["candidate"], result["candidate"]));
        Assert.Empty(result["executed"]!.AsArray());
        Assert.Empty(result["artifacts"]!.AsArray());
        Assert.Equal("not-required", result["stages"]!["current"]!["status"]!.GetValue<string>());
        Assert.Equal(0, fixture.Cli("validate-no-work", "--commit", fixture.Commit, "--changes", fixture.Manifest,
            "--plan", fixture.Plan, "--result", fixture.Result).ExitCode);
        fixture.AssertNoTools();
    }

    [Fact]
    public void SharedCanonicalCasesAgreeAcrossNativeLoaderAndLightProcess()
    {
        var data = FileMapPlanningFixture.Canonical;
        foreach (var item in data["cases"]!.AsArray())
        {
            var path = item!["path"]!.GetValue<string>();
            using var fixture = new FileMapPlanningFixture();
            fixture.Supply(fixture.Changes(path));
            var result = fixture.MakePlan();
            if (item["require"] is null)
            {
                Assert.Equal(2, result.ExitCode);
                Assert.Contains(path, FileMapPlanningFixture.Text(result), StringComparison.Ordinal);
            }
            else
            {
                Assert.True(result.ExitCode == 0, FileMapPlanningFixture.Text(result));
                Assert.True(JsonNode.DeepEquals(item["require"], FileMapPlanningFixture.Read(fixture.Plan)["declared_require"]));
            }
            fixture.AssertNoTools();
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void MixedChangesUnionDeclaredResourcesAndPureCheckRequestsNoCache(bool pureCheck)
    {
        using var fixture = new FileMapPlanningFixture();
        fixture.Supply(fixture.Changes(pureCheck ? ["one/check.txt"] : ["README.md", "D5/a.lean", "tools/a.cs"]));
        var result = fixture.MakePlan();
        Assert.True(result.ExitCode == 0, FileMapPlanningFixture.Text(result));
        var plan = FileMapPlanningFixture.Read(fixture.Plan);
        Assert.Equal(pureCheck ? ["build", "filemap"] : new[] { "build", "engineering", "lean-report" }, Strings(plan["resources"]));
        Assert.Equal(pureCheck ? [] : new[] { "dependency", "judge", "project", "report" }, Strings(plan["cache_layers"]));
        Assert.Equal(2, fixture.NoWork().ExitCode);
        Assert.Equal(2, fixture.NoWork("current").ExitCode);
        fixture.AssertNoTools();
    }

    [Theory]
    [InlineData("missing-require")]
    [InlineData("unknown-resource")]
    [InlineData("cycle")]
    [InlineData("same-stage-cycle")]
    [InlineData("missing-material")]
    [InlineData("unregistered-owner")]
    [InlineData("invalid-owner")]
    [InlineData("name-newline")]
    [InlineData("numeric-projection-mode")]
    [InlineData("duplicate-resource")]
    [InlineData("duplicate-field")]
    [InlineData("invalid-stage")]
    [InlineData("invalid-cache")]
    [InlineData("invalid-pattern")]
    [InlineData("invalid-mode")]
    public void InvalidDeclarationsFailInBothConsumers(string mutation)
    {
        var source = FileMapPlanningFixture.Canonical["filemap"]!.GetValue<string>();
        source = mutation switch
        {
            "missing-require" => source.Replace("require = []\n", "", StringComparison.Ordinal),
            "unknown-resource" => source.Replace("require = []", "require = [\"unknown\"]", StringComparison.Ordinal),
            "cycle" => source.Replace("prerequisites = []", "prerequisites = [\"engineering\"]", StringComparison.Ordinal),
            "same-stage-cycle" => source.Replace("prerequisites = []", "prerequisites = [\"lean-report\"]", StringComparison.Ordinal)
                .Replace("stage = \"build\"", "stage = \"current\"", StringComparison.Ordinal)
                .Replace("stage = \"engineering\"", "stage = \"current\"", StringComparison.Ordinal),
            "missing-material" => source.Replace("materials = []", "materials = [\"tools/missing.py\"]", StringComparison.Ordinal),
            "unregistered-owner" => source.Replace("owner = \"tools/owner.py\"", "owner = \"unregistered.py\"", StringComparison.Ordinal),
            "invalid-owner" => source.Replace("owner = \"tools/owner.py\"", "owner = \"tools/../README.md\"", StringComparison.Ordinal),
            "name-newline" => source.Replace("consumed_by = [\"reader\"]", "consumed_by = [\"reader\\n\"]", StringComparison.Ordinal),
            "numeric-projection-mode" => NumericProjectionMode(source),
            "duplicate-resource" => source.Replace("id = \"engineering\"", "id = \"build\"", StringComparison.Ordinal),
            "duplicate-field" => source.Replace("schema_version = 3", "schema_version = 3\nschema_version = 3", StringComparison.Ordinal),
            "invalid-stage" => source.Replace("stage = \"current\"", "stage = \"unknown\"", StringComparison.Ordinal),
            "invalid-cache" => source.Replace("cache_layers = []", "cache_layers = [\"unknown\"]", StringComparison.Ordinal),
            "invalid-pattern" => source.Replace("one/*.txt", "one/?.txt", StringComparison.Ordinal),
            _ => source + "mode = \"120000\"\n",
        };
        using var fixture = new FileMapPlanningFixture(source);
        if (mutation == "unregistered-owner") { fixture.Write("unregistered.py", "# unregistered\n"); fixture.Save(); }
        fixture.Supply(fixture.Changes("README.md"));
        // The write-set operation uses the real strict loader without unrelated
        // whole-repository policy findings from this deliberately small fixture.
        Assert.Equal(2, FileMapConformCommand.Run(["--producer-write-set", "none"], fixture.Root).ExitCode);
        Assert.Equal(2, fixture.MakePlan().ExitCode);
        fixture.AssertNoTools();
    }

    [Fact]
    public void StageNoWorkAcceptsOnlyAnUnneededStageOfAValidatedPlan()
    {
        using var fixture = new FileMapPlanningFixture();
        fixture.Supply(fixture.Changes("one/check.txt"));
        Assert.Equal(0, fixture.MakePlan().ExitCode);
        Assert.Equal(0, fixture.Cli("validate-plan", "--commit", fixture.Commit, "--changes", fixture.Manifest,
            "--plan", fixture.Plan).ExitCode);
        Assert.Equal(0, fixture.NoWork("engineering").ExitCode);
        Assert.Equal("not-required", FileMapPlanningFixture.Read(fixture.Result)["status"]!.GetValue<string>());
        Assert.Equal(0, fixture.Cli("validate-no-work", "--commit", fixture.Commit, "--changes", fixture.Manifest,
            "--plan", fixture.Plan, "--result", fixture.Result, "--stage", "engineering").ExitCode);
        Assert.Equal(2, fixture.NoWork("delta").ExitCode);
        Assert.Equal(2, fixture.NoWork("build").ExitCode);
        fixture.AssertNoTools();
    }

    [Fact]
    public void DeclaredUnicodeMaterialsUseTheSameOrdinalOrderInBothConsumers()
    {
        const string first = "tools/material-\U0001F600";
        const string second = "tools/material-\uE000";
        var source = FileMapPlanningFixture.Canonical["filemap"]!.GetValue<string>()
            .Replace("materials = []", $"materials = [\"{first}\", \"{second}\"]", StringComparison.Ordinal);
        using var fixture = new FileMapPlanningFixture(source);
        fixture.Write(first, "first\n"); fixture.Write(second, "second\n"); fixture.Save();
        fixture.Supply(fixture.Changes("one/check.txt"));
        Assert.Equal(0, FileMapConformCommand.Run(["--producer-write-set", "none"], fixture.Root).ExitCode);
        Assert.Equal(0, fixture.MakePlan().ExitCode);
        Assert.Equal(new[] { "Meta/ci-checks.json", "Meta/ci-resources.json", "Meta/engineering-projects.json", first, second }, Strings(FileMapPlanningFixture.Read(fixture.Plan)["materials"]));
        fixture.AssertNoTools();
    }

    [Fact]
    public void ConflictingMatchesNameTheExactPathEvenWhenRequirementsAgree()
    {
        var source = FileMapPlanningFixture.Canonical["filemap"]!.GetValue<string>();
        source = source.Replace("pattern = \"one/*.txt\"", "pattern = \"docs/**\"", StringComparison.Ordinal);
        // Keep the canonical ordering while introducing the deliberate overlap.
        var prefix = source[..source.IndexOf("\n[[files]]", StringComparison.Ordinal)];
        var rows = source[prefix.Length..].Split("\n[[files]]", StringSplitOptions.RemoveEmptyEntries).Order(StringComparer.Ordinal);
        source = prefix + string.Concat(rows.Select(row => "\n[[files]]" + row));
        const string path = "docs/reports/白 纸.md";
        using var fixture = new FileMapPlanningFixture(source);
        fixture.Supply(fixture.Changes(path));
        var result = fixture.MakePlan();
        Assert.Equal(2, result.ExitCode);
        Assert.Contains(path, FileMapPlanningFixture.Text(result), StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("complete")]
    [InlineData("count")]
    [InlineData("candidate")]
    [InlineData("tree")]
    [InlineData("mode")]
    [InlineData("path")]
    [InlineData("status")]
    [InlineData("duplicate-path")]
    [InlineData("unexpected-field")]
    public void InvalidCompleteScopeFailsBeforeAnyExpensiveWork(string mutation)
    {
        using var fixture = new FileMapPlanningFixture();
        var changes = fixture.Changes("README.md");
        var record = changes["changes"]![0]!;
        switch (mutation)
        {
            case "complete": changes["complete"] = false; break;
            case "count": changes["change_count"] = 2; break;
            case "candidate": changes["candidate"]!["commit"] = new string('a', 40); break;
            case "tree": changes["candidate"]!["tree"] = new string('a', 40); break;
            case "mode": record["new"]!["mode"] = "120000"; break;
            case "path": record["new"]!["path"] = "docs/../README.md"; break;
            case "status": record["status"] = "M"; break;
            case "duplicate-path": changes["changes"]!.AsArray().Add(record.DeepClone()); changes["change_count"] = 2; break;
            default: changes["extra"] = true; break;
        }
        fixture.Supply(changes);
        Assert.Equal(2, fixture.MakePlan().ExitCode);
        fixture.AssertNoTools();
    }

    [Theory]
    [InlineData("missing-plan")]
    [InlineData("failed-plan")]
    [InlineData("wrong-result-candidate")]
    [InlineData("fake-artifact")]
    [InlineData("duplicate-json-field")]
    [InlineData("wrong-json-type")]
    public void NoWorkNeverAcceptsMissingFailedOrMismatchedEvidence(string mutation)
    {
        using var fixture = new FileMapPlanningFixture();
        fixture.Supply(fixture.Changes("README.md"));
        Assert.Equal(0, fixture.MakePlan().ExitCode);
        Assert.Equal(0, fixture.NoWork().ExitCode);
        if (mutation == "missing-plan") TemporaryFileSystem.File.Delete(fixture.Plan);
        else if (mutation == "failed-plan")
        {
            var plan = FileMapPlanningFixture.Read(fixture.Plan); plan["status"] = "failed";
            TemporaryFileSystem.File.WriteAllText(fixture.Plan, plan.ToJsonString());
        }
        else
        {
            var result = FileMapPlanningFixture.Read(fixture.Result);
            if (mutation == "wrong-result-candidate") result["candidate"]!["commit"] = new string('b', 40);
            if (mutation == "fake-artifact") result["artifacts"]!.AsArray().Add("fake.dll");
            if (mutation == "wrong-json-type") result["exit"] = false;
            var text = result.ToJsonString();
            if (mutation == "duplicate-json-field") text = "{\"status\":\"not-required\"," + text[1..];
            TemporaryFileSystem.File.WriteAllText(fixture.Result, text);
        }
        Assert.Equal(2, fixture.Cli("validate-no-work", "--commit", fixture.Commit, "--changes", fixture.Manifest,
            "--plan", fixture.Plan, "--result", fixture.Result).ExitCode);
        fixture.AssertNoTools();
    }

    private static string[] Strings(JsonNode? value) => value!.AsArray().Select(item => item!.GetValue<string>()).ToArray();

    private static string NumericProjectionMode(string source)
    {
        var last = source.LastIndexOf("[[files]]", StringComparison.Ordinal);
        return source[..last] + source[last..]
            .Replace("kind = \"program\"", "kind = \"generated\"", StringComparison.Ordinal)
            .Replace("produced_by = \"none\"", "produced_by = \"FixtureProducer\"", StringComparison.Ordinal)
            .Replace("verified_by = [\"dotnet-test\"]", "verified_by = [\"FixtureProducer\"]", StringComparison.Ordinal)
            .Replace("artifact_id = \"none\"", "artifact_id = \"fixture-artifact\"", StringComparison.Ordinal)
            + "mode = 100644\nhistory_requirement = \"not-required\"\n";
    }
}
