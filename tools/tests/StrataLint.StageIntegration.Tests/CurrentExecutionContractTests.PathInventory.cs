using StrataLint.EngineeringScope;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.StageIntegration.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("body", false)]
    [InlineData("add", true)]
    [InlineData("untracked", true)]
    [InlineData("ignored", false)]
    [InlineData("delete", true)]
    [InlineData("remove", true)]
    [InlineData("rename", true)]
    [InlineData("mode", true)]
    [InlineData("index-mode", true)]
    [InlineData("untrack", true)]
    public void RegisteredInventoryReusesOnlyUnchangedPathMetadata(string mutation, bool invalidates)
    {
        if (OperatingSystem.IsWindows() && mutation is "mode" or "index-mode") return;
        using var fixture = new ExecutionFixture();
        RegisterInventory(fixture);
        fixture.Write("fixtures/subject.txt", "original\n");
        fixture.Track();
        Assert.Equal(new[] { ExecutionFixture.First, ExecutionFixture.Second }, Execute(fixture));
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root);
        var subject = Path.Combine(fixture.Root, "fixtures/subject.txt");
        switch (mutation)
        {
            case "body": fixture.Write("fixtures/subject.txt", "new body\n"); break;
            case "add": fixture.Write("fixtures/added.txt", "new\n"); fixture.Track(); break;
            case "untracked": fixture.Write("fixtures/added.txt", "new\n"); break;
            case "ignored": fixture.Write("build/ignored.txt", "new\n"); break;
            case "delete": File.Delete(subject); break;
            case "remove": EngineeringProcess.Git(fixture.Root, "rm", "-f", "--", "fixtures/subject.txt"); break;
            case "rename": File.Move(subject, Path.Combine(fixture.Root, "fixtures/renamed.txt")); break;
            case "mode":
                if (!OperatingSystem.IsWindows()) File.SetUnixFileMode(subject, File.GetUnixFileMode(subject) | UnixFileMode.UserExecute);
                break;
            case "index-mode": EngineeringProcess.Git(fixture.Root, "update-index", "--chmod=+x", "fixtures/subject.txt"); break;
            case "untrack": EngineeringProcess.Git(fixture.Root, "rm", "--cached", "fixtures/subject.txt"); break;
        }
        Assert.Equal(invalidates ? new[] { ExecutionFixture.First } : [], Execute(fixture));
        var current = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Assert.Equal(invalidates, prior.Projects[0].InputFingerprint != current.Projects[0].InputFingerprint);
        Assert.Equal(invalidates ? "executed" : "reused", current.Projects[0].Status);
        Assert.Equal(prior.Projects[1] with { Status = "reused" }, current.Projects[1]);
    }

    [Fact]
    public void InventoryFingerprintIncludesSymlinkTargetWithoutOrdinaryTargetBody()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ExecutionFixture();
        fixture.Write("fixtures/first.txt", "same\n");
        fixture.Write("fixtures/second.txt", "same\n");
        RegisterInventory(fixture, "first.txt");
        File.CreateSymbolicLink(Path.Combine(fixture.Root, "fixtures/alias"), "first.txt");
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        fixture.Write("fixtures/first.txt", "ordinary target body changed\n");
        Assert.Empty(Execute(fixture));
        Seed(fixture);
        File.Delete(Path.Combine(fixture.Root, "fixtures/alias"));
        File.CreateSymbolicLink(Path.Combine(fixture.Root, "fixtures/alias"), "second.txt");
        RegisterInventory(fixture, "second.txt");
        Assert.Equal(new[] { ExecutionFixture.First }, Execute(fixture));
    }

    [Fact]
    public void IndexOnlyMetadataMutationDuringTestsRejectsExecutionEvidence()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ExecutionFixture();
        RegisterInventory(fixture);
        fixture.Write("fixtures/subject.txt", "same\n");
        fixture.Track();
        fixture.Build();
        var failure = Assert.Throws<InvalidDataException>(() => Program.RunCurrentTests(fixture.Root, (project, results) =>
        {
            fixture.WriteTrx(results, "Passed");
            EngineeringProcess.Git(fixture.Root, "update-index", "--chmod=+x", "fixtures/subject.txt");
            return 0;
        }, TextWriter.Null));
        Assert.Contains("candidate changed during test execution", failure.Message, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("project-mismatch")]
    [InlineData("resource-mismatch")]
    [InlineData("unmapped-resource")]
    [InlineData("non-ci")]
    public void InventoryDeclarationsMustAgreeBeforeAnySelectedTest(string defect)
    {
        using var fixture = new ExecutionFixture();
        RegisterInventory(fixture);
        fixture.Write("fixtures/subject.txt", "same\n");
        if (defect is "project-mismatch" or "non-ci")
            EditRegistration(fixture, rows => rows[0]![defect == "non-ci" ? "ci" : "execution_path_inventory"] =
                defect == "non-ci" ? JsonValue.Create(false) : new JsonArray("other/**"));
        else if (defect == "resource-mismatch")
            fixture.Write("Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"))
                .Replace("path_inventory = [\"fixtures/**\"]", "path_inventory = [\"other/**\"]", StringComparison.Ordinal));
        else
            fixture.Write("Meta/ci-resources.json", "{\"schema\":\"ci-resource-execution-v1\",\"resources\":[{\"id\":\"inventory\",\"projects\":[],\"checks\":[],\"steps\":[]}]}");
        fixture.Track();
        Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.TestInputs(fixture.Root,
            CommonExecutionEvidence.Snapshot(fixture.Root), [ExecutionFixture.Second]));
    }

    [Theory]
    [InlineData("non-ci")]
    [InlineData("empty-binding")]
    public void BodyTriggerDeclarationsRequireCiTestMappingsEvenWhenUnselected(string defect)
    {
        using var fixture = new ExecutionFixture();
        RegisterInventory(fixture);
        EditRegistration(fixture, rows => rows[0]!["execution_path_inventory"] = new JsonArray());
        fixture.Write("Meta/FILEMAP.toml", File.ReadAllText(Path.Combine(fixture.Root, "Meta/FILEMAP.toml"))
            .Replace("path_inventory =", "path_inputs =", StringComparison.Ordinal));
        if (defect == "non-ci") EditRegistration(fixture, rows => rows[0]!["ci"] = false);
        else fixture.Write("Meta/ci-resources.json", "{\"schema\":\"ci-resource-execution-v1\",\"resources\":[{\"id\":\"inventory\",\"projects\":[],\"checks\":[],\"steps\":[]}]}");
        fixture.Track();
        var error = Assert.Throws<InvalidDataException>(() => CommonExecutionEvidence.TestInputs(fixture.Root,
            CommonExecutionEvidence.Snapshot(fixture.Root), [ExecutionFixture.Second]));
        Assert.Contains("path_inputs", error.Message, StringComparison.Ordinal);
    }

    private static void RegisterInventory(ExecutionFixture fixture, string? linkTarget = null)
    {
        EditRegistration(fixture, rows => rows[0]!["execution_path_inventory"] = new JsonArray("fixtures/**"));
        fixture.Write("Meta/ci-resources.json", "{\"schema\":\"ci-resource-execution-v1\",\"resources\":[{\"id\":\"inventory\",\"projects\":[\""
            + ExecutionFixture.First + "\"],\"checks\":[],\"steps\":[]}]}");
        var patterns = new[] { ".gitignore", "Meta/**", "fixtures/*.txt", "global.json", "tools/**" };
        string Entry(string pattern, string? target = null) => "[[files]]\npattern = \"" + pattern
            + "\"\nrequire = []\nkind = \"program\"\nadmission_plane = \"judge\"\nproduced_by = \"none\"\nconsumed_by = [\"test\"]\nverified_by = [\"test\"]\nartifact_id = \"none\"\nruntime_disposition = \"committed-source\"\n"
            + (target is null ? "" : "symlink = { target = \"" + target + "\", kind = \"file\" }\n");
        fixture.Write("Meta/FILEMAP.toml", """
            schema_version = 5
            resources = [{ id = "inventory", stage = "engineering", owner = "global.json", prerequisites = [], tools = [], cache_layers = [], cache_activation = {}, materials = [], path_inventory = ["fixtures/**"] }]
            evidence = { artifact_kinds = { json = { profile = "structured-json", selectors = ["result"], path_selectors = ["formal"] } } }
            [residence_policy]
            case_id = "FIXTURE"
            desired = "registered"
            known_violation_count = 0
            status = "closed"
            """ + "\n" + string.Concat(patterns.Append(linkTarget is null ? null : "fixtures/alias").OfType<string>()
                .Order(StringComparer.Ordinal).Select(pattern => Entry(pattern, pattern == "fixtures/alias" ? linkTarget : null))));
    }
}
