using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed partial class SelfLockProbeScriptTests
{
    [Theory]
    [InlineData("tools/scripts/workflow/pure-revert-detect.sh")]
    [InlineData("tools/scripts/workflow/self-lock-probe.sh")]
    [InlineData("tools/StrataLint.EngineeringScope/SelfLockProbe/ProbeReducer.cs")]
    [InlineData("tools/StrataLint.EngineeringScope/TestResultEvidence.cs")]
    [InlineData("tools/StrataLint.Engine/Admission/BootstrapProtectionPolicy.cs")]
    [InlineData("tools/scripts/report/report-supervisor.sh")]
    [InlineData("tools/tests/StrataLint.ScriptTests/SelfLockProbeScriptTests.Decisions.cs")]
    [InlineData("tools/self-lock-probe-result.json")]
    public void RevertTouchingProbeOwnerClosureIsTrueRed(string path)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture(revertedPath: path);

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }

    [Fact]
    public void WorkflowCarrierInOwnerClosureIsTrueRed()
    {
        if (OperatingSystem.IsWindows()) return;
        var path = ".github/" + "work" + "flows/ci.yml";
        using var fixture = new ProbeFixture(revertedPath: path);

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }

    [Fact]
    public void CandidateAuthoredResultAndMarkersCannotAuthorize()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.WriteCandidateMarker(
            "tools/forged-self-lock-result.json",
            "{\"decision\":\"self_lock_confirmed\",\"allow_exact_revert\":true}\n");
        fixture.J0Bundle.RemoveFinalizationSentinel();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void DuplicateJsonKeysAreIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        var json = fixture.J0Bundle.Supervisor.ToJsonString();
        var duplicate = json.Replace(
            "\"schema_version\":1",
            "\"schema_version\":1,\"schema_version\":1",
            StringComparison.Ordinal);
        fixture.J0Bundle.WriteRawSupervisorAndBind(duplicate);

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void ControlCharactersInIdentityAreIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.Supervisor["blockers"]![0]!["test_id"] = "bad\u0001identity";
        fixture.J0Bundle.Supervisor["required_identities"]![0]!["test_id"] = "bad\u0001identity";
        fixture.J0Bundle.WriteRawSupervisorAndBind(
            fixture.J0Bundle.Supervisor.ToJsonString(JsonOptions));

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void TrxPathNormalizationCollisionIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.Supervisor["trx_artifacts"] = new JsonArray(
            new JsonObject
            {
                ["file_name"] = "engineering.trx",
                ["assembly"] = ExpectedAssembly,
                ["sha256"] = "sha256:" + new string('a', 64),
            },
            new JsonObject
            {
                ["file_name"] = "dir/../engineering.trx",
                ["assembly"] = ExpectedAssembly,
                ["sha256"] = "sha256:" + new string('a', 64),
            });
        fixture.J0Bundle.WriteRawSupervisorAndBind(
            fixture.J0Bundle.Supervisor.ToJsonString(JsonOptions));

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void SupervisorSchemaWithUnknownMemberIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J1Bundle.Supervisor["candidate_conclusion"] = "success";
        fixture.J1Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void NonPureRevertIsTrueRed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        var marker = Path.Combine(fixture.CandidateRepository, "tools", "policy-under-test.txt");
        ScriptHarnessScratch.WriteScratchText(marker, "not the inverse\n");
        GitAt(fixture.CandidateRepository, "add", "tools/policy-under-test.txt");
        GitAt(fixture.CandidateRepository, "commit", "--amend", "--no-edit");

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "TRUE_RED_CONFIRMED",
            allowExactRevert: false,
            exitCode: 1);
    }
}
