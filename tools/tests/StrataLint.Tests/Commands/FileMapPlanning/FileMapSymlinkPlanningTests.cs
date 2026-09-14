using System.Text.Json.Nodes;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class FileMapSymlinkPlanningTests
{
    [Theory]
    [InlineData("file")]
    [InlineData("directory")]
    public void DeclaredAliasesDoNotPreventUnrelatedDocsFromSelectingNoResources(string kind)
    {
        using var fixture = Create(kind);
        var changes = fixture.Changes("docs/reports/note.md");
        fixture.Supply(changes);

        var result = fixture.MakePlan();

        Assert.True(result.ExitCode == 0, FileMapPlanningFixture.Text(result));
        var plan = FileMapPlanningFixture.Read(fixture.Plan);
        Assert.Empty(plan["resources"]!.AsArray());
        Assert.Empty(plan["cache_layers"]!.AsArray());
        Assert.Single(plan["paths"]!.AsArray());
        Assert.Equal(0, fixture.NoWork().ExitCode);
        fixture.AssertNoTools();
    }

    [Theory]
    [InlineData("file", false)]
    [InlineData("file", true)]
    [InlineData("directory", false)]
    [InlineData("directory", true)]
    public void PrAliasAdditionAndDeletionPreserveLinkBytesAndRegisteredWork(string kind, bool deleted)
    {
        using var fixture = Create(kind);
        if (!deleted) { fixture.Git("rm", "Alias"); fixture.Save(); }
        var baseline = fixture.Commit;
        if (deleted) fixture.Git("rm", "Alias");
        else Link(fixture, kind);
        fixture.Save();
        var head = fixture.Commit;
        var tree = fixture.Git("rev-parse", "HEAD^{tree}").Trim();
        var merge = fixture.Git("commit-tree", tree, "-p", baseline, "-p", head, "-m", "candidate").Trim();

        var produced = fixture.Cli("pr-paths", "--commit", merge, "--base", baseline,
            "--head", head, "--output", fixture.Manifest);

        Assert.True(produced.ExitCode == 0, FileMapPlanningFixture.Text(produced));
        var change = Assert.Single(FileMapPlanningFixture.Read(fixture.Manifest)["changes"]!.AsArray());
        Assert.Equal(deleted ? "D" : "A", change!["status"]!.ToString());
        Assert.Equal("120000", change[deleted ? "old" : "new"]!["mode"]!.ToString());
        var planned = fixture.MakePlan(merge);
        Assert.True(planned.ExitCode == 0, FileMapPlanningFixture.Text(planned));
        Assert.Equal(new[] { "build", "filemap" }, FileMapPlanningFixture.Read(fixture.Plan)["resources"]!
            .AsArray().Select(value => value!.ToString()).ToArray());
        fixture.AssertNoTools();
    }

    [Theory]
    [InlineData("target-bytes")]
    [InlineData("missing-target")]
    [InlineData("undeclared")]
    [InlineData("chain")]
    public void InvalidAliasSnapshotFailsBeforeAResourceFreeResult(string defect)
    {
        using var fixture = Create("file");
        if (defect == "target-bytes")
        {
            File.Delete(Path.Combine(fixture.Root, "Alias"));
            File.CreateSymbolicLink(Path.Combine(fixture.Root, "Alias"), "tools/owner.py");
        }
        else if (defect == "missing-target") fixture.Git("rm", "README.md");
        else if (defect == "chain")
        {
            File.Delete(Path.Combine(fixture.Root, "README.md"));
            File.CreateSymbolicLink(Path.Combine(fixture.Root, "README.md"), "tools/owner.py");
        }
        else fixture.Write("Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml")).Replace(
            "symlink = { target = \"README.md\", kind = \"file\" }\n", "", StringComparison.Ordinal));
        fixture.Save();
        fixture.Supply(fixture.Changes("docs/reports/note.md"));

        var result = fixture.MakePlan();

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("symlink", FileMapPlanningFixture.Text(result), StringComparison.Ordinal);
        Assert.False(File.Exists(fixture.Plan));
        fixture.AssertNoTools();
    }

    [Fact]
    public void PrRegularFileBecomingAnAliasPreservesBothEndpointModes()
    {
        using var fixture = Create("file");
        File.Delete(Path.Combine(fixture.Root, "Alias"));
        fixture.Write("Alias", "regular file\n");
        fixture.Save();
        var baseline = fixture.Commit;
        File.Delete(Path.Combine(fixture.Root, "Alias"));
        Link(fixture, "file");
        fixture.Save();
        var head = fixture.Commit;
        var tree = fixture.Git("rev-parse", "HEAD^{tree}").Trim();
        var merge = fixture.Git("commit-tree", tree, "-p", baseline, "-p", head, "-m", "candidate").Trim();

        var result = fixture.Cli("pr-paths", "--commit", merge, "--base", baseline,
            "--head", head, "--output", fixture.Manifest);

        Assert.True(result.ExitCode == 0, FileMapPlanningFixture.Text(result));
        var change = Assert.Single(FileMapPlanningFixture.Read(fixture.Manifest)["changes"]!.AsArray());
        Assert.Equal("M", change!["status"]!.ToString());
        Assert.Equal("100644", change["old"]!["mode"]!.ToString());
        Assert.Equal("120000", change["new"]!["mode"]!.ToString());
        var planned = fixture.MakePlan(merge);
        Assert.True(planned.ExitCode == 0, FileMapPlanningFixture.Text(planned));
        Assert.Equal(new[] { "build", "filemap" }, FileMapPlanningFixture.Read(fixture.Plan)["resources"]!
            .AsArray().Select(value => value!.ToString()).ToArray());
        fixture.AssertNoTools();
    }

    [Fact]
    public void LocalDirectoryAliasRetainsRawLinkOidWithoutDuplicateDescendantInputs()
    {
        using var fixture = Create("directory");
        fixture.Write(".git/info/exclude", "/build/\n");
        var oid = fixture.Git("rev-parse", "HEAD:Alias").Trim();

        var result = fixture.Cli("push-plan", "--commit", fixture.Commit);

        Assert.True(result.ExitCode == 0, FileMapPlanningFixture.Text(result));
        var scope = FileMapPlanningFixture.Read(Path.Combine(fixture.Root, "build/ci/changes.json"));
        var links = scope["changes"]!.AsArray().Select(row => row!["new"]!).ToArray();
        var alias = Assert.Single(links, row => row["path"]!.ToString() == "Alias");
        Assert.Equal("120000", alias["mode"]!.ToString());
        Assert.Equal(oid, alias["oid"]!.ToString());
        Assert.DoesNotContain(links, row => row["path"]!.ToString().StartsWith("Alias/", StringComparison.Ordinal));
        var plan = FileMapPlanningFixture.Read(Path.Combine(fixture.Root, "build/ci/plan.json"));
        Assert.DoesNotContain(plan["paths"]!.AsArray(), row => row!["path"]!.ToString().StartsWith("Alias/", StringComparison.Ordinal));
        fixture.AssertNoTools();
    }

    [Fact]
    public void LocalIndexedInputCannotReadThroughADirectorySymlinkAncestor()
    {
        using var fixture = Create("file");
        Directory.Delete(Path.Combine(fixture.Root, "docs/reports"), recursive: true);
        Directory.CreateSymbolicLink(Path.Combine(fixture.Root, "docs/reports"), "../../tools");

        var result = fixture.Cli("push-plan", "--commit", fixture.Commit);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("symlink ancestor", FileMapPlanningFixture.Text(result), StringComparison.Ordinal);
        Assert.False(File.Exists(Path.Combine(fixture.Root, "build/ci/plan.json")));
        fixture.AssertNoTools();
    }

    private static FileMapPlanningFixture Create(string kind)
    {
        var source = Manifest(kind);
        var fixture = new FileMapPlanningFixture(source);
        fixture.Write("docs/reports/target.md", "target\n");
        Link(fixture, kind);
        fixture.Save();
        Assert.Equal(0, FileMapConformCommand.Run(["--producer-write-set", "none"], fixture.Root).ExitCode);
        return fixture;
    }

    private static void Link(FileMapPlanningFixture fixture, string kind) =>
        File.CreateSymbolicLink(Path.Combine(fixture.Root, "Alias"), Target(kind));

    private static string Target(string kind) => kind == "file" ? "README.md" : "docs/reports";

    private static string Manifest(string kind)
    {
        var source = FileMapPlanningFixture.Canonical["filemap"]!.GetValue<string>();
        var offset = source.IndexOf("[[files]]", StringComparison.Ordinal);
        var row = $$"""
            [[files]]
            pattern = "Alias"
            require = ["filemap"]
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["agent"]
            verified_by = ["repository-policy"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            symlink = { target = "{{Target(kind)}}", kind = "{{kind}}" }

            """;
        return source.Insert(offset, row + "\n");
    }
}
