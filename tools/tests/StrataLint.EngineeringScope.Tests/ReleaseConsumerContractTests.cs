using static StrataLint.TestSupport.NativeReleaseFixture;
using System.IO.Compression;
using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class ReleaseConsumerContractTests
{
    [Fact]
    public void OriginalProducerEnvironmentVerifiesButCannotSupplyLocalReuse()
    {
        using var fixture = new ResourceFixture(["filemap", "lean-report"]);
        var previous = Environment.GetEnvironmentVariable("DOTNET_PROCESSOR_COUNT");
        CommonStageRecord original;
        try
        {
            // A real native consumer runs with a different registered process count.
            // This injects an environment difference; it is not a cross-OS Actions run.
            Environment.SetEnvironmentVariable("DOTNET_PROCESSOR_COUNT", "1");
            fixture.Processes(bindPlan: false);
            fixture.CompleteCheckBoundary();
            using var output = new StringWriter();
            Assert.True(fixture.Run("current", output, planned: false) == 0, output.ToString());
            original = CommonExecutionEvidence.ValidateCurrent(fixture.Root);
            Assert.True(CommonExecutionEvidence.ExportCheckSeed(fixture.Root, "current", TextWriter.Null));
            Pack(fixture, 17);
        }
        finally { Environment.SetEnvironmentVariable("DOTNET_PROCESSOR_COUNT", previous); }
        var before = original.Materials.ToDictionary(m => m.Path, m => CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, m.Path)));
        var result = Native(fixture.Root, ["transport-verify", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "1"], "2");
        Capture(fixture.Root, "producer-environment", result);
        Assert.True(result.Exit == 0, result.Text);
        Assert.Contains("status=verified", result.Text, StringComparison.Ordinal);
        var reuse = Native(fixture.Root, ["check-seed-import", "--repository", fixture.Root, "--stage", "current"], "2");
        Capture(fixture.Root, "local-reuse", reuse);
        Assert.True(reuse.Exit == 0, reuse.Text);
        Assert.Contains("COMMON_CHECK_SEED_MISS id=filemap", reuse.Text, StringComparison.Ordinal);
        Assert.DoesNotContain("COMMON_CHECK_REUSED id=filemap", reuse.Text, StringComparison.Ordinal);
        var compatible = Native(fixture.Root, ["check-seed-import", "--repository", fixture.Root, "--stage", "current"], "1");
        Capture(fixture.Root, "compatible-local-reuse", compatible);
        Assert.True(compatible.Exit == 0, compatible.Text);
        Assert.Contains("COMMON_CHECK_REUSED id=filemap", compatible.Text, StringComparison.Ordinal);
        foreach (var material in before)
            Assert.Equal(material.Value, CommonExecutionEvidence.Hash(Path.Combine(fixture.Root, material.Key)));
    }

    [Theory]
    [InlineData("environment")]
    [InlineData("sdk")]
    [InlineData("candidate")]
    [InlineData("round")]
    [InlineData("material")]
    public void BoundMalformedProducerEvidenceCannotVerify(string damage)
    {
        using var fixture = new ResourceFixture(["filemap"]);
        Produce(fixture);
        Pack(fixture, 17);
        var checksPath = CommonExecutionEvidence.ChecksPath("current");
        var checks = Read(fixture.Root, checksPath);
        var unit = checks["units"]![0]!;
        if (damage == "environment") unit["execution_environment"] = "not-json";
        if (damage == "sdk") unit["execution_environment"] = CommonExecutionEvidence.ExecutionEnvironment(fixture.Root)
            .Replace("10.0.103", "0.0.0", StringComparison.Ordinal);
        if (damage == "candidate") unit["execution_candidate"] = new string('a', 64);
        if (damage == "round") unit["execution_round"] = "other-round";
        if (damage == "material") File.AppendAllText(Path.Combine(fixture.Root, unit["operations"]![0]!["log"]!.ToString()), "corrupt");
        else File.WriteAllText(Path.Combine(fixture.Root, checksPath), checks.ToJsonString());
        // Rebind the outer material hashes so the original-unit validator is tested.
        Rebind(fixture.Root, CommonExecutionEvidence.CurrentPath, checksPath);
        Rebind(fixture.Root, CiTransport.ManifestPath("current"), checksPath, CommonExecutionEvidence.CurrentPath);
        var result = Native(fixture.Root, ["transport-verify", "--repository", fixture.Root, "--stage", "current",
            "--commit", fixture.Commit, "--run-id", "17", "--run-attempt", "1"]);
        Capture(fixture.Root, "malformed-" + damage, result);
        Assert.Equal(2, result.Exit);
        Assert.DoesNotContain("status=verified", result.Text, StringComparison.Ordinal);
    }

}
