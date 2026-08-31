using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed partial class SelfLockProbeScriptTests
{
    [Fact]
    public void NonAtomicPublicationIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.Supervisor["publication"] = "incremental";
        fixture.J0Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void UnsupportedSupervisorSchemaIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.Supervisor["schema_version"] = 2;
        fixture.J0Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void UnregisteredFailureKeyIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        foreach (var bundle in new[] { fixture.J1Bundle, fixture.J0Bundle })
        {
            bundle.Supervisor["failure_keys"] = new JsonArray("UNREGISTERED_FAILURE");
            bundle.Supervisor["blockers"]![0]!["failure_key"] = "UNREGISTERED_FAILURE";
            bundle.Publish();
        }

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void NonPassingTrxIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.TrxText = CompleteTrx([PresentTest])
            .Replace("outcome=\"Passed\"", "outcome=\"Failed\"", StringComparison.Ordinal)
            .Replace("passed=\"1\"", "passed=\"0\"", StringComparison.Ordinal)
            .Replace("failed=\"0\"", "failed=\"1\"", StringComparison.Ordinal);
        fixture.J0Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void CopiedAuthorizedBundleAtUnreceiptedPathIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.CopyToUnreceiptedPath(
            System.IO.Path.Combine(System.IO.Path.GetDirectoryName(fixture.J0Bundle.Path)!, "forged-j0"));

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void ProducerDigestMustComeFromControllerBase()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.TamperAuthorityProducerDigest();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void PublicationPointerMustBindFinalSentinel()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.TamperPublicationSentinelDigest();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }
}
