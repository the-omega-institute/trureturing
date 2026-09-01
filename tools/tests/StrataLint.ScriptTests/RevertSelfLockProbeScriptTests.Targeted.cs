using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed partial class RevertSelfLockProbeScriptTests
{
    [Fact]
    public void RealControllerExtractsOneCanonicalBlockerRecord()
    {
        var temporary = Directory.CreateTempSubdirectory();
        using var fixture = new TargetedCommandFixture(temporary);
        var result = fixture.ExtractBlockers(
            "prefix ENGINEERING_TEST_EVIDENCE_FAILED TRX is missing protected-base planned "
            + "test identities count=1 tests=Example.Tests::ExampleTests.Missing\n");

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        var output = JsonNode.Parse(File.ReadAllText(
            Path.Combine(temporary.FullName, "blockers.json")))!.AsObject();
        Assert.Equal(1, output["schema_version"]!.GetValue<int>());
        var blocker = Assert.Single(output["blockers"]!.AsArray())!.AsObject();
        Assert.Equal("Example.Tests", blocker["assembly"]!.GetValue<string>());
        Assert.Equal("ExampleTests.Missing", blocker["test_id"]!.GetValue<string>());
    }

    [Fact]
    public void RealTargetedRunnerWritesSemanticMissingEvidenceFromFilteredTrx()
    {
        var temporary = Directory.CreateTempSubdirectory();
        using var fixture = new TargetedCommandFixture(temporary);

        var result = fixture.RunTargeted();

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        Assert.Empty(result.StandardError);
        var supervisor = JsonNode.Parse(File.ReadAllText(Path.Combine(
            temporary.FullName, "bundle", ".staging", "supervisor-result.json")))!.AsObject();
        Assert.Equal("synthetic_noop", supervisor["subject"]!["kind"]!.GetValue<string>());
        Assert.Equal(
            "ENGINEERING_TEST_EVIDENCE_FAILED",
            Assert.Single(supervisor["failure_keys"]!.AsArray())!.GetValue<string>());
        var blocker = Assert.Single(supervisor["blockers"]!.AsArray())!.AsObject();
        Assert.Equal("missing_identity", blocker["kind"]!.GetValue<string>());
        Assert.Equal("ExampleTests.Missing", blocker["test_id"]!.GetValue<string>());
        var normalizedTrx = File.ReadAllText(Path.Combine(
            temporary.FullName, "bundle", ".staging", "trx", "engineering-000.trx"));
        Assert.Contains("ExampleTests.Present", normalizedTrx, StringComparison.Ordinal);
        Assert.DoesNotContain("ExampleTests.Missing", normalizedTrx, StringComparison.Ordinal);
    }
}
