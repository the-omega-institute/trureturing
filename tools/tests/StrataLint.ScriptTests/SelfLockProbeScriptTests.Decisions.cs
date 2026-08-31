namespace StrataLint.Tests;

public sealed partial class SelfLockProbeScriptTests
{
    [Fact]
    public void GenuineEngineeringMissingIdentitySelfLockIsConfirmed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "SELF_LOCK_CONFIRMED",
            allowExactRevert: true,
            exitCode: 0);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SyntheticNoopOidAndParentShapeDoNotChangeDecision(bool mergeShapedNoop)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture(mergeShapedNoop: mergeShapedNoop);

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "SELF_LOCK_CONFIRMED",
            allowExactRevert: true,
            exitCode: 0);
    }

    [Fact]
    public void EmptyRedGateSetIsTrueRed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();

        AssertDecision(
            RunProbe(fixture, ["engineering"], []),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }

    [Fact]
    public void EmptyRedGateSetWithAdmittedJ1IsTrueRed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J1Bundle.Supervisor["termination"] = new System.Text.Json.Nodes.JsonObject
        {
            ["kind"] = "exited",
            ["exit_code"] = 0,
            ["signal"] = null,
        };
        fixture.J1Bundle.Supervisor["failure_keys"] = new System.Text.Json.Nodes.JsonArray();
        fixture.J1Bundle.Supervisor["required_identities"] = new System.Text.Json.Nodes.JsonArray(
            EvidenceBundle.Identity(PresentTest));
        fixture.J1Bundle.Supervisor["blockers"] = new System.Text.Json.Nodes.JsonArray();
        fixture.J1Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], []),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }

    [Fact]
    public void UnmatchedBaseBlockerIsTrueRed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.Supervisor["blockers"] = new System.Text.Json.Nodes.JsonArray(
            EvidenceBundle.Blocker("Engineering.Tests.DifferentIdentity"));
        fixture.J0Bundle.Supervisor["required_identities"] = new System.Text.Json.Nodes.JsonArray(
            EvidenceBundle.Identity("Engineering.Tests.DifferentIdentity"),
            EvidenceBundle.Identity(PresentTest));
        fixture.J0Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }

    [Fact]
    public void IncompleteCoverageIsTrueRed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.Supervisor["required_identities"]!.AsArray().Add(
            EvidenceBundle.Identity("Engineering.Tests.ExtraRequiredIdentity"));
        fixture.J0Bundle.Supervisor["blockers"]!.AsArray().Add(
            EvidenceBundle.Blocker("Engineering.Tests.ExtraRequiredIdentity"));
        fixture.J0Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }

    [Fact]
    public void DelimiterCollisionDoesNotCreateEquivalentBlockers()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        var j1 = EvidenceBundle.Blocker("C");
        j1["assembly"] = "A|B";
        var j0 = EvidenceBundle.Blocker("B|C");
        j0["assembly"] = "A";
        fixture.J1Bundle.Supervisor["blockers"] = new System.Text.Json.Nodes.JsonArray(j1);
        fixture.J1Bundle.Supervisor["required_identities"] = new System.Text.Json.Nodes.JsonArray(
            new System.Text.Json.Nodes.JsonObject { ["assembly"] = "A|B", ["test_id"] = "C" },
            EvidenceBundle.Identity(PresentTest));
        fixture.J0Bundle.Supervisor["blockers"] = new System.Text.Json.Nodes.JsonArray(j0);
        fixture.J0Bundle.Supervisor["required_identities"] = new System.Text.Json.Nodes.JsonArray(
            new System.Text.Json.Nodes.JsonObject { ["assembly"] = "A", ["test_id"] = "B|C" },
            EvidenceBundle.Identity(PresentTest));
        fixture.J1Bundle.Publish();
        fixture.J0Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }

    [Fact]
    public void LeanGateIsUnsupportedAndDenied()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();

        AssertDecision(
            RunProbe(fixture, ["engineering", "lean"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void AdmissionGateIsUnsupportedAndDenied()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();

        AssertDecision(
            RunProbe(fixture, ["engineering", "admission"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void IndeterminateDecisionUsesTheDenyBranch()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.RemoveFinalizationSentinel();

        var output = RunProbe(fixture, ["engineering"], ["engineering"]);

        AssertDecision(
            output,
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
        Assert.DoesNotContain("SELF_LOCK_CONFIRMED", ParseResult(output).Decision, StringComparison.Ordinal);
    }
}
