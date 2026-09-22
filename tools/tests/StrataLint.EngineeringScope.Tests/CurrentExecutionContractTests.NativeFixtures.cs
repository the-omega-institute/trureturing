using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

public sealed partial class CurrentExecutionContractTests
{
    [Theory]
    [InlineData("tools/lean-inspector/native_image.c", true)]
    [InlineData("Makefile", true)]
    [InlineData("README.md", false)]
    public void RegisteredNativeFixtureInputsRerunConsumedFilesAndReuseUnrelatedChanges(string path, bool invalidates)
    {
        using var fixture = new CandidateFixture();
        var registration = JsonNode.Parse(File.ReadAllText(Path.Combine(TestRepositoryLayout.FindRoot(), EngineeringRegistrationFixture.Path)))!;
        var declaration = registration["projects"]!.AsArray().Single(row => row!["path"]!.ToString()
            == "tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj")!;
        EditRegistration(fixture, rows =>
        {
            foreach (var field in new[] { "execution_inputs", "execution_excludes", "execution_environment" })
                rows[0]![field] = declaration[field]!.DeepClone();
        });
        // Use the real execution declaration with synthetic compile inputs and
        // runner results, so only the consumed file changes between executions.
        foreach (var input in declaration["execution_inputs"]!.AsArray().Select(value => value!.ToString()).Where(value => !value.Contains('*')))
            if (!File.Exists(Path.Combine(fixture.Root, input))) fixture.Write(input, "registered fixture material\n");
        fixture.Write(path, "original fixture input\n");
        fixture.Track();
        Assert.Equal(new[] { CandidateFixture.First, CandidateFixture.Second }, Execute(fixture));
        var original = CommonExecutionEvidence.ValidateTests(fixture.Root);
        Seed(fixture);

        fixture.Write(path, "changed fixture input\n");
        fixture.Track();

        var calls = Execute(fixture);
        var current = CommonExecutionEvidence.ValidateTests(fixture.Root);
        var prior = original.Projects[0];
        var accepted = current.Projects[0];
        Assert.True(calls.SequenceEqual(invalidates ? new[] { CandidateFixture.First } : []),
            $"[FAIL] native_fixture_execution_input: {path}: invalidates={invalidates}; executed={string.Join(',', calls)}; old={prior.InputFingerprint}; new={accepted.InputFingerprint}");
        if (invalidates)
        {
            Assert.NotEqual(prior.InputFingerprint, accepted.InputFingerprint);
            Assert.Equal("executed", accepted.Status);
            Assert.Equal(current.Candidate, accepted.ExecutionCandidate);
            Assert.Equal(current.Round, accepted.ExecutionRound);
        }
        else Assert.Equal(prior with { Status = "reused" }, accepted);
        Assert.Equal(original.Projects[1] with { Status = "reused" }, current.Projects[1]);
    }
}
