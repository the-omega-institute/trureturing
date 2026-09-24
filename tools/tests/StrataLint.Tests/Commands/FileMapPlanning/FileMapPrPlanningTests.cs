using System.Text.Json.Nodes;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.EngineeringScope;

namespace StrataLint.Tests;

public sealed class FileMapPrPlanningTests
{
    [Theory]
    [InlineData("push")]
    [InlineData("pr")]
    public void LibraryOnlyPlanSelectsConformanceThatRejectsAnUnregisteredDomain(string mode)
    {
        using var fixture = FileMapPlanningFixture.LibraryPolicy();
        var basis = fixture.Commit;
        const string path = "Library/UnknownDomain/reference.md";
        fixture.Write(path, "citation-only reference\n");
        fixture.Save();
        var head = fixture.Commit;
        string planPath;
        if (mode == "push")
        {
            var planned = fixture.Cli("push-plan", "--commit", head, "--before", basis, "--after", head);
            Assert.True(planned.ExitCode == 0, FileMapPlanningFixture.Text(planned));
            planPath = Path.Combine(fixture.Root, "build/ci/plan.json");
        }
        else
        {
            var merge = fixture.Git("commit-tree", fixture.Git("rev-parse", "HEAD^{tree}").Trim(),
                "-p", basis, "-p", head, "-m", "library candidate").Trim();
            fixture.Git("checkout", "--detach", merge);
            var produced = fixture.Cli("pr-paths", "--commit", merge, "--base", basis, "--head", head,
                "--output", fixture.Manifest);
            Assert.True(produced.ExitCode == 0, FileMapPlanningFixture.Text(produced));
            var planned = fixture.MakePlan(merge);
            Assert.True(planned.ExitCode == 0, FileMapPlanningFixture.Text(planned));
            planPath = fixture.Plan;
        }

        var plan = FileMapPlanningFixture.Read(planPath);
        Assert.Equal(path, Assert.Single(plan["paths"]!.AsArray())!["path"]!.ToString());
        Assert.Equal(new[] { "filemap", "scribe" }, plan["declared_require"]!.AsArray().Select(value => value!.ToString()));
        Assert.Empty(plan["execution"]!["tests"]!.AsArray());
        Assert.Equal(new[] { "filemap", "scribe-describe", "scribe-markdown", "scribe-projections" },
            plan["execution"]!["checks"]!.AsArray().Select(value => value!.ToString()));
        var checks = FileMapPlanningFixture.Read(Path.Combine(fixture.Root, "Meta/ci-checks.json"));
        var registration = checks["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "filemap")!["delta_scope"]!
            .Deserialize<RegisteredFileMapScope>(new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower });
        var scope = FileMapInspectionScope.Select(registration,
            plan["paths"]!.AsArray().Select(row => row!["path"]!.ToString()).ToArray(), FileMapPolicy.TrackedPaths(fixture.Root));
        Assert.Equal(new[] { path }, scope.Paths);
        File.WriteAllText(fixture.Result, JsonSerializer.Serialize(scope,
            new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower }));
        var rejected = FileMapPolicy.InspectRepository(fixture.Root, scope);
        var finding = Assert.Single(rejected, row => row.Code == "FILEMAP-PATH-POLICY");
        Assert.Equal(path, finding.Path);
        Assert.Contains("registry artifact kind/selector whitelist", finding.Message, StringComparison.Ordinal);
        var result = FileMapConformCommand.Run(["--scope", fixture.Result], fixture.Root);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains($"FILEMAP-PATH-POLICY {path}:", result.Output, StringComparison.Ordinal);

        fixture.Write("Meta/domains.yaml", TestRegistry.Domains
            + "  UnknownDomain:\n    stratum: S3\n    definition: Registered fixture domain.\n");
        var accepted = FileMapPolicy.InspectRepository(fixture.Root, scope);
        Assert.DoesNotContain(accepted, row => row.Code == "FILEMAP-PATH-POLICY");
        Assert.Equal(rejected.Where(row => row != finding), accepted);
        fixture.AssertNoTools();
    }

    [Theory]
    [InlineData("Library/notes/reference.md", false)]
    [InlineData("Library/Carrier/nested/reference.md", true)]
    public void LibraryPathPolicyPreservesNotesAndRejectsNoncanonicalShapeWithinSelectedScope(string path, bool rejected)
    {
        using var fixture = FileMapPlanningFixture.LibraryPolicy();
        fixture.Write(path, "reference\n");
        const string unrelated = "Library/UnknownDomain/unselected.md";
        fixture.Write(unrelated, "unselected reference\n");
        fixture.Save();
        var selected = FileMapPolicy.InspectRepository(fixture.Root, new FileMapInspectionScope([path], Actors: false));
        Assert.Equal(rejected, selected.Any(row => row.Code == "FILEMAP-PATH-POLICY" && row.Path == path));
        Assert.DoesNotContain(selected, row => row.Code == "FILEMAP-PATH-POLICY" && row.Path == unrelated);
        Assert.Contains(FileMapPolicy.InspectRepository(fixture.Root),
            row => row.Code == "FILEMAP-PATH-POLICY" && row.Path == unrelated);
    }

    [Fact]
    public void PinnedPrProducerPreservesAddDeleteRenameModeAndWhitespaceOnDivergentHead()
    {
        using var fixture = new FileMapPlanningFixture();
        fixture.Write("docs/reports/old name 白.md", "rename content\n");
        fixture.Write("docs/reports/deleted.md", "delete content\n");
        fixture.Save();
        var fork = fixture.Commit;
        fixture.Write("docs/reports/base-only.md", "base\n"); fixture.Save();
        var basis = fixture.Commit;
        fixture.Git("checkout", "--detach", fork);
        fixture.Git("mv", "docs/reports/old name 白.md", "docs/reports/new name 白.md");
        fixture.Git("rm", "docs/reports/deleted.md");
        fixture.Git("update-index", "--chmod=+x", "README.md");
        fixture.Git("commit", "-qm", "rename delete mode");
        fixture.Write("docs/reports/added 白.md", "new\n"); fixture.Save();
        // Save stages the working mode, so apply the mode-only change last.
        fixture.Git("update-index", "--chmod=+x", "README.md");
        fixture.Git("commit", "-qm", "mode");
        var head = fixture.Commit;
        var tree = fixture.Git("merge-tree", "--write-tree", basis, head).Trim();
        var merge = fixture.Git("commit-tree", tree, "-p", basis, "-p", head, "-m", "merge fixture").Trim();
        var produced = fixture.Cli("pr-paths", "--commit", merge, "--base", basis, "--head", head, "--output", fixture.Manifest);
        Assert.True(produced.ExitCode == 0, FileMapPlanningFixture.Text(produced));
        var manifest = FileMapPlanningFixture.Read(fixture.Manifest);
        Assert.True(manifest["complete"]!.GetValue<bool>());
        Assert.Equal(basis, manifest["base"]!.GetValue<string>());
        var records = manifest["changes"]!.AsArray();
        Assert.Equal(4, records.Count);
        Assert.Contains(records, item => item!["status"]!.GetValue<string>() == "R"
            && item["old"]!["path"]!.GetValue<string>() == "docs/reports/old name 白.md"
            && item["new"]!["path"]!.GetValue<string>() == "docs/reports/new name 白.md");
        Assert.Contains(records, item => item!["status"]!.GetValue<string>() == "D");
        Assert.Contains(records, item => item!["status"]!.GetValue<string>() == "A");
        Assert.Contains(records, item => item!["status"]!.GetValue<string>() == "M"
            && item["old"]!["mode"]!.GetValue<string>() == "100644"
            && item["new"]!["mode"]!.GetValue<string>() == "100755");
        Assert.Equal(0, fixture.MakePlan(merge).ExitCode);
        Assert.Equal(5, FileMapPlanningFixture.Read(fixture.Plan)["paths"]!.AsArray().Count);
        foreach (var stage in new[] { "engineering", "current", "delta" })
        {
            Assert.Equal(0, fixture.Cli("no-work", "--commit", merge, "--changes", fixture.Manifest,
                "--plan", fixture.Plan, "--stage", stage, "--output", fixture.Result).ExitCode);
            var noWork = FileMapPlanningFixture.Read(fixture.Result);
            Assert.Equal("not-required", noWork["status"]!.GetValue<string>());
            Assert.Equal(merge, noWork["candidate"]!["commit"]!.GetValue<string>());
            Assert.Empty(noWork["executed"]!.AsArray());
            Assert.Empty(noWork["artifacts"]!.AsArray());
            Assert.Equal(0, fixture.Cli("validate-no-work", "--commit", merge, "--changes", fixture.Manifest,
                "--plan", fixture.Plan, "--stage", stage, "--result", fixture.Result).ExitCode);
        }
        // A syntactically complete, truncated PR manifest is independently rejected.
        records.RemoveAt(0); manifest["change_count"] = records.Count; fixture.Supply(manifest);
        Assert.Equal(2, fixture.MakePlan(merge).ExitCode);
        Assert.Equal(2, fixture.Cli("pr-paths", "--commit", merge, "--base", fork, "--head", head,
            "--output", fixture.Manifest).ExitCode);
        fixture.AssertNoTools();
    }

    [Fact]
    public void MissingManifestAndInvalidCandidateNeverSelectAllWork()
    {
        using var fixture = new FileMapPlanningFixture();
        Assert.Equal(2, fixture.MakePlan().ExitCode);
        fixture.Supply(fixture.Changes("README.md"));
        Assert.Equal(2, fixture.MakePlan("HEAD").ExitCode);
        var source = TemporaryFileSystem.File.ReadAllText(fixture.Manifest);
        TemporaryFileSystem.File.WriteAllText(fixture.Manifest, "{\"complete\":true," + source[1..]);
        Assert.Equal(2, fixture.MakePlan().ExitCode);
        fixture.AssertNoTools();
    }
}
