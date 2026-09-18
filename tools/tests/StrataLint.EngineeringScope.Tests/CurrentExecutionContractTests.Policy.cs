using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("CLAUDE.md", true)]
    [InlineData("skills/codex-formal-answer/SKILL.md", true)]
    [InlineData("skills/codex-theory-ingest/SKILL.md", true)]
    [InlineData("tools/scripts/agent/batch_pr.sh", true)]
    [InlineData("Meta/domains.yaml", true)]
    [InlineData("Meta/registry.yaml", true)]
    [InlineData("Meta/judge-seed.json", true)]
    [InlineData("Meta/package-materials.json", true)]
    [InlineData("tools/scripts/agent/merge-gate.sh", false)]
    public void RegisteredRepositoryContractsInvalidateOnlyTheirDeclaredMaterials(string path, bool invalidates)
    {
        using var fixture = new CandidateFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.Repository.Tests/StrataLint.Repository.Tests.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        foreach (var input in declaration["execution_inputs"]!.AsArray().Select(value => value!.ToString()).Where(value => !value.Contains('*')))
            if (!File.Exists(Path.Combine(fixture.Root, input))) fixture.Write(input, input == "Meta/FILEMAP.toml"
                ? "schema_version = 4\n[[files]]\npattern = \"tools/tests/First/**\"\nkind = \"program\"\n"
                : "registered fixture material\n");
        fixture.Write(path, "original input\n");
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root).Projects[0];

        fixture.Write(path, "changed input\n");
        fixture.Track();

        Assert.Equal(invalidates ? new[] { CandidateFixture.First } : [], Execute(fixture));
        var accepted = CommonExecutionEvidence.ValidateTests(fixture.Root).Projects[0];
        if (invalidates) Assert.NotEqual(prior.InputFingerprint, accepted.InputFingerprint);
        else Assert.Equal(prior with { Status = "reused" }, accepted);
    }
}
