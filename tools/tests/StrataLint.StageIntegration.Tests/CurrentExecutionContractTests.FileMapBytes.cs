using System.Text.Json.Nodes;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.StageIntegration.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("comment", false)]
    [InlineData("unrelated-row", false)]
    [InlineData("queried-row", true)]
    public void ExplicitFileMapQueriesKeepTheirProjectionIdentity(string mutation, bool invalidates)
    {
        using var fixture = new ExecutionFixture();
        const string filemap = "schema_version = 5\n[[files]]\npattern = \"docs/virtual.md\"\nrequire = []\n";
        fixture.Write("Meta/FILEMAP.toml", filemap);
        EditRegistration(fixture, rows =>
        {
            rows[0]!["execution_inputs"] = new JsonArray("Meta/FILEMAP.toml");
            rows[0]!["execution_filemap_paths"] = new JsonArray("docs/virtual.md");
        });
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root);
        fixture.Write("Meta/FILEMAP.toml", mutation switch
        {
            "comment" => filemap + "# cp " + string.Concat('-', 'c') + " fixture\n",
            "unrelated-row" => filemap + "[[files]]\npattern = \"unrelated/**\"\nrequire = []\n",
            _ => filemap.Replace("require = []", "require = [\"engineering\"]", StringComparison.Ordinal),
        });
        Assert.Equal(invalidates ? [ExecutionFixture.First] : [], Execute(fixture));
        var current = CommonExecutionEvidence.ValidateTests(fixture.Root);
        if (invalidates) Assert.NotEqual(prior.Projects[0].InputFingerprint, current.Projects[0].InputFingerprint);
        else Assert.Equal(prior.Projects[0] with { Status = "reused" }, current.Projects[0]);
        Assert.Equal(prior.Projects[1] with { Status = "reused" }, current.Projects[1]);
        AcceptEngineering(fixture);
        CommonExecutionEvidence.ValidateEngineering(fixture.Root);
    }

    [Theory]
    [InlineData("README.md", false)]
    [InlineData("Meta/FILEMAP.toml", false)]
    [InlineData("Makefile", true)]
    [InlineData("tools/Makefile", true)]
    [InlineData("tools/scripts/linkage-probe.sh", true)]
    [InlineData(".github/scripts/linkage-probe.sh", true)]
    public void CliLinkageRuntimeInputsExcludeUnrelatedRepositoryText(string path, bool invalidates)
    {
        using var fixture = new ExecutionFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.RepositoryContract.Tests/StrataLint.RepositoryContract.Tests.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes", "execution_filemap_paths" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        const string filemap = """
            schema_version = 5
            resources = []
            evidence = { artifact_kinds = { json = { profile = "structured-json", selectors = ["result"], path_selectors = ["formal"] } } }
            [residence_policy]
            case_id = "FIXTURE"
            desired = "registered"
            known_violation_count = 0
            status = "closed"
            [[files]]
            pattern = "**"
            require = []
            kind = "program"
            admission_plane = "judge"
            produced_by = "none"
            consumed_by = ["test"]
            verified_by = ["test"]
            artifact_id = "none"
            runtime_disposition = "committed-source"
            """ + "\n";
        foreach (var input in new[] {
            "README.md", "Meta/FILEMAP.toml", "Makefile", "tools/Makefile",
            "tools/scripts/linkage-probe.sh", ".github/scripts/linkage-probe.sh",
        }) fixture.Write(input, input == "Meta/FILEMAP.toml" ? filemap : "registered fixture input\n");
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root);
        File.AppendAllText(Path.Combine(fixture.Root, path), "# changed caller bytes\n");
        Assert.Equal(invalidates ? [ExecutionFixture.First] : [], Execute(fixture));
        var current = CommonExecutionEvidence.ValidateTests(fixture.Root);
        if (invalidates) Assert.NotEqual(prior.Projects[0].InputFingerprint, current.Projects[0].InputFingerprint);
        else Assert.Equal(prior.Projects[0] with { Status = "reused" }, current.Projects[0]);
        Assert.Equal(prior.Projects[1] with { Status = "reused" }, current.Projects[1]);
        AcceptEngineering(fixture);
    }

}
