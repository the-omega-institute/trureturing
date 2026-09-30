using System.Text.Json.Nodes;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.EngineeringScope;
using StrataLint.FileMap;
using StrataLint.Scribe.Documents;

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
        var checks = FileMapPlanningFixture.Read(Path.Combine(fixture.Root, "Meta/ci-checks.json"));
        var registration = checks["checks"]!.AsArray().Single(row => row!["id"]!.ToString() == "filemap")!["delta_scope"]!
            .Deserialize<RegisteredFileMapScope>(new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower });
        var scope = FileMapInspectionScope.Select(registration,
            plan["paths"]!.AsArray().Select(row => row!["path"]!.ToString()).ToArray(), FileMapPolicy.TrackedPaths(fixture.Root));
        Assert.Equal(new[] { path }, scope.Paths);
        File.WriteAllText(fixture.Result, JsonSerializer.Serialize(scope,
            new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower }));
        var documentPaths = DocumentAssembly.Definitions.Select(static definition => definition.RelativePath.Value);
        var rejected = FileMapPolicy.InspectRepository(fixture.Root, documentPaths, scope);
        var finding = Assert.Single(rejected, row => row.Code == "FILEMAP-PATH-POLICY");
        Assert.Equal(path, finding.Path);
        Assert.Contains("controlled domain vocabulary", finding.Message, StringComparison.Ordinal);
        var result = FileMapConformCommand.Run(["--scope", fixture.Result], fixture.Root);
        Assert.Equal(1, result.ExitCode);
        Assert.Contains($"FILEMAP-PATH-POLICY {path}:", result.Output, StringComparison.Ordinal);

        fixture.Write("Meta/domains.yaml", TestFileMap.Domains
            + "  UnknownDomain:\n    stratum: S3\n    definition: Registered fixture domain.\n");
        var accepted = FileMapPolicy.InspectRepository(fixture.Root, documentPaths, scope);
        Assert.DoesNotContain(accepted, row => row.Code == "FILEMAP-PATH-POLICY");
        Assert.Equal(rejected.Where(row => row != finding), accepted);
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
        var documentPaths = DocumentAssembly.Definitions.Select(static definition => definition.RelativePath.Value);
        var selected = FileMapPolicy.InspectRepository(fixture.Root, documentPaths, new FileMapInspectionScope([path], Actors: false));
        Assert.Equal(rejected, selected.Any(row => row.Code == "FILEMAP-PATH-POLICY" && row.Path == path));
        Assert.DoesNotContain(selected, row => row.Code == "FILEMAP-PATH-POLICY" && row.Path == unrelated);
        Assert.Contains(FileMapPolicy.InspectRepository(fixture.Root, documentPaths),
            row => row.Code == "FILEMAP-PATH-POLICY" && row.Path == unrelated);
    }

}
