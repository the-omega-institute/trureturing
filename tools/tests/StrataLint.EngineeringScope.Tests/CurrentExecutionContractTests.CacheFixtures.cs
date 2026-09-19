using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("D5/S0/CacheInputProbe.lean", false)]
    [InlineData("Blueprint/CacheInputProbe.scribe.cs", false)]
    [InlineData("Meta/Digestion/backfill/cache-input-probe.json", false)]
    [InlineData("Meta/domains.yaml", false)]
    [InlineData("Meta/registry.yaml", false)]
    [InlineData("tools/scripts/agent/openproblem/templates/judgement-form-check-template.md", false)]
    [InlineData("tools/scripts/agent/openproblem/templates/learner-brief.md", false)]
    [InlineData("tools/scripts/agent/openproblem/templates/impl-base-brief.md", false)]
    [InlineData("tools/scripts/agent/openproblem/lane.sh", false)]
    [InlineData("tools/tests/StrataLint.Tests/Commands/WorktreeCommandTests.cs", false)]
    [InlineData("tools/scripts/worktree/lean_actions.py", true)]
    [InlineData("tools/scripts/worktree/lean_cache_release.py", true)]
    [InlineData("tools/scripts/workflow/ci.py", true)]
    [InlineData("tools/scripts/report/dotnet_producer.py", true)]
    [InlineData("tools/scripts/lib/resource-observation-lib.sh", true)]
    [InlineData("Makefile", true)]
    [InlineData("tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py", true)]
    public void RegisteredCacheFixtureInputsReuseContentChangesAndRerunCacheChanges(string path, bool invalidates)
    {
        using var fixture = new CandidateFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.Cache.Tests/StrataLint.Cache.Tests.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        const string documents = "tools/fixture/BlueprintFixture.csproj";
        fixture.Write(documents, "<Project />\n");
        var manifest = Path.Combine(fixture.Root, EngineeringRegistrationFixture.Path);
        File.WriteAllText(manifest, EngineeringRegistrationFixture.Append(File.ReadAllText(manifest),
            new EngineeringProjectFixture(documents, "BlueprintFixture", "test-support", false, ["Blueprint/**/*.scribe.cs"])));
        const string unrelatedTests = "tools/tests/StrataLint.Tests/StrataLint.Tests.csproj";
        fixture.Write(unrelatedTests, "<Project />\n");
        File.WriteAllText(manifest, EngineeringRegistrationFixture.Append(File.ReadAllText(manifest),
            new EngineeringProjectFixture(unrelatedTests, "UnrelatedTests", "test-support", false, ["tools/tests/StrataLint.Tests/**/*.cs"])));
        foreach (var input in declaration["execution_inputs"]!.AsArray().Select(value => value!.ToString()).Where(value => !value.Contains('*')))
            if (!File.Exists(Path.Combine(fixture.Root, input))) fixture.Write(input, input == "Meta/FILEMAP.toml"
                ? "schema_version = 4\n[[files]]\npattern = \"tools/tests/First/**\"\nkind = \"program\"\n"
                : "registered fixture material\n");
        fixture.Write(path, "original registered input\n");
        fixture.Track();
        Execute(fixture);
        Seed(fixture);
        var prior = CommonExecutionEvidence.ValidateTests(fixture.Root).Projects[0];

        fixture.Write(path, "changed registered input\n");
        fixture.Track();

        var calls = Execute(fixture);
        Assert.True(calls.SequenceEqual(invalidates ? new[] { CandidateFixture.First } : []),
            $"[FAIL] cache_fixture_input_isolation: {path}: invalidates={invalidates}; executed={string.Join(',', calls)}");
        var accepted = CommonExecutionEvidence.ValidateTests(fixture.Root).Projects[0];
        if (invalidates) Assert.NotEqual(prior.InputFingerprint, accepted.InputFingerprint);
        else Assert.Equal(prior with { Status = "reused" }, accepted);
    }
}
