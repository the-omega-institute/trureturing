using System.Text.Json;
using Trureturing.Truth;
using Xunit;

namespace StrataLint.TruthRelease.Tests;

public sealed partial class TruthReleaseCommandTests
{
    [Fact]
    public void InstalledTruthReleaseAllowsVerifiedTruthWithUnrelatedBrokenReceipt()
    {
        using var fixture = CreateFixture(receiptIntegrityMismatch: true, productionVerifier: true);
        using var output = new TemporaryDirectory();
        var (exitCode, console) = Run(fixture, output.Path, GreenTrustArguments());
        Assert.True(exitCode == 0, console.Error);
        var publication = TruthReleasePublicationReader.Read(File.ReadAllBytes(
            Path.Combine(output.Path, TruthReleaseBundleWriter.PublicationFileName)));
        var verified = TruthReleasePublicationVerification.Verify(output.Path, publication);
        Assert.Equal(6, verified.Manifest.Artifacts.GetType().GetProperties().Length);
        Assert.Equal(2, verified.ReadTruthExport().Nodes.Length);
        Assert.False(File.Exists(Path.Combine(output.Path, "echo-residual-summary.md")));
        using var snapshot = JsonDocument.Parse(File.ReadAllBytes(Path.Combine(output.Path,
            TruthReleaseBundleWriter.SourceSnapshotFileName)));
        Assert.Equal("source-snapshot.v2", snapshot.RootElement.GetProperty("schema").GetString());
        Assert.False(snapshot.RootElement.TryGetProperty("residual_frontier_sha256", out _));
    }
}
