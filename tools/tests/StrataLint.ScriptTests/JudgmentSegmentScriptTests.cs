using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class JudgmentSegmentScriptTests
{
    private static readonly string[] EvidenceKeys =
    [
        "schema_version", "segment", "event", "merge_commit", "tree", "base",
        "source_head", "raw_rc", "outcome", "report_input_address", "report_sha256",
        "judge_source_address", "scribe_source_address", "selected_test_ids",
        "ordered_check_ids",
    ];

    [Fact]
    public void LeanInspectSegmentSuccessPublishesCompleteEvidence()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();

        var result = fixture.RunLeanInspect();

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "lean-inspect", 0, "passed");
        AssertResolvedIdentity(sentinel, fixture);
        var reportInputAddress =
            sentinel.RootElement.GetProperty("report_input_address").GetString();
        Assert.Equal(fixture.CanonicalReportInputAddress, reportInputAddress);
        Assert.NotEqual(fixture.RepositoryInputAddress, reportInputAddress);
        Assert.Matches("^[0-9a-f]{64}$",
            sentinel.RootElement.GetProperty("report_sha256").GetString());
        Assert.Matches("^[0-9a-f]{64}$",
            sentinel.RootElement.GetProperty("scribe_source_address").GetString());
        Assert.Equal(JsonValueKind.Null,
            sentinel.RootElement.GetProperty("judge_source_address").ValueKind);
        Assert.Equal(JsonValueKind.Null,
            sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
        Assert.Equal(
            ["produce-canonical-lean-report", "scribe-content-checks"],
            sentinel.RootElement.GetProperty("ordered_check_ids").EnumerateArray()
                .Select(static item => item.GetString()));
        Assert.Equal(Utf8(result.StandardOutput), fixture.LeanEvidenceText);
    }

    [Fact]
    public void AdmissionSegmentSuccessInheritsLeanEvidence()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);

        var result = fixture.RunAdmission();

        Assert.True(result.ExitCode == 0, Diagnostics(result));
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "admission", 0, "passed");
        AssertResolvedIdentity(sentinel, fixture);
        var reportInputAddress =
            sentinel.RootElement.GetProperty("report_input_address").GetString();
        Assert.Equal(fixture.CanonicalReportInputAddress, reportInputAddress);
        Assert.NotEqual(fixture.RepositoryInputAddress, reportInputAddress);
        Assert.Matches("^[0-9a-f]{64}$",
            sentinel.RootElement.GetProperty("report_sha256").GetString());
        Assert.Matches("^[0-9a-f]{64}$",
            sentinel.RootElement.GetProperty("judge_source_address").GetString());
        Assert.Equal(
            JsonDocument.Parse(fixture.LeanEvidenceText).RootElement
                .GetProperty("scribe_source_address").GetString(),
            sentinel.RootElement.GetProperty("scribe_source_address").GetString());
        Assert.Equal(
            ["verify-lean-inspect-evidence", "harness-gate"],
            sentinel.RootElement.GetProperty("ordered_check_ids").EnumerateArray()
                .Select(static item => item.GetString()));
        Assert.Contains("--base", fixture.RecordedCalls, StringComparison.Ordinal);
        Assert.Contains("--candidate-lean-report", fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionSegmentAcceptsProtectedSurfaceChange()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);

        var result = fixture.RunAdmission(gateExitCode: 3);

        Assert.Equal(0, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "admission", 3, "protected-surface-change");
    }

    [Fact]
    public void JudgmentSegmentPrIdentitiesMatchBothFixtureParents()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture(createMergeCommit: true);

        var leanResult = fixture.RunLeanInspect(eventName: "PR");
        Assert.Equal(0, leanResult.ExitCode);
        using var leanSentinel = AssertSingleSentinel(leanResult);
        AssertResolvedIdentity(leanSentinel, fixture);

        var admissionResult = fixture.RunAdmission(eventName: "PR");
        Assert.Equal(0, admissionResult.ExitCode);
        using var admissionSentinel = AssertSingleSentinel(admissionResult);
        AssertResolvedIdentity(admissionSentinel, fixture);
    }

    [Fact]
    public void AdmissionSegmentRejectsMissingLeanEvidence()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);
        fixture.DeleteLeanEvidence();

        var result = fixture.RunAdmission();

        Assert.Equal(2, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "admission", 2, "report-evidence-mismatch");
        Assert.DoesNotContain("gate:", fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionSegmentRejectsMismatchedLeanEvidence()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);
        fixture.TamperLeanEvidenceReportHash();

        var result = fixture.RunAdmission();

        Assert.Equal(2, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "admission", 2, "report-evidence-mismatch");
        Assert.DoesNotContain("gate:", fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionSegmentRejectsLeanEvidenceFromDifferentHead()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);
        fixture.TamperLeanEvidenceMergeCommit();

        var result = fixture.RunAdmission();

        Assert.Equal(2, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "admission", 2, "report-evidence-mismatch");
        Assert.DoesNotContain("gate:", fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void LeanInspectSegmentReusesValidCachedReport()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        fixture.WriteValidCachedReport();

        var result = fixture.RunLeanInspect();

        Assert.Equal(0, result.ExitCode);
        Assert.DoesNotContain("pair:", fixture.RecordedCalls, StringComparison.Ordinal);
        Assert.Equal("cached report\n", File.ReadAllText(fixture.ReportPath));
    }

    [Theory]
    [InlineData("provenance-address")]
    [InlineData("report-sha")]
    [InlineData("input-attestation")]
    [InlineData("materials-zip")]
    public void LeanInspectSegmentFullyReproducesOnceForInvalidCachedBundle(string damage)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        fixture.WriteCachedReportWithDamage(damage);

        var result = fixture.RunLeanInspect();

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            1,
            fixture.RecordedCalls.Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Count(static line => line.StartsWith("pair:", StringComparison.Ordinal)));
        Assert.Equal("fixture report\n", File.ReadAllText(fixture.ReportPath));
    }

    [Fact]
    public void LeanInspectSegmentFallsBackFromAddressMismatchedScribeBinary()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        fixture.WriteMismatchedScribeAttestation();

        var result = fixture.RunLeanInspect();

        Assert.Equal(0, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        Assert.Equal(
            JudgmentSegmentFixture.ScribeSourceAddress,
            sentinel.RootElement.GetProperty("scribe_source_address").GetString());
        Assert.DoesNotContain(fixture.ScribeDllPath, fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void LeanInspectSegmentRejectsMalformedScribeBinaryAttestation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        fixture.WriteMalformedScribeAttestation();

        var result = fixture.RunLeanInspect();

        Assert.Equal(2, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(
            sentinel,
            "lean-inspect",
            2,
            "scribe-address-verification-failed");
        Assert.DoesNotContain("scribe:", fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionSegmentFallsBackFromAddressMismatchedJudgeBinary()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);
        fixture.WriteMismatchedJudgeAttestation();

        var result = fixture.RunAdmission();

        Assert.Equal(0, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        Assert.Equal(
            JudgmentSegmentFixture.JudgeSourceAddress,
            sentinel.RootElement.GetProperty("judge_source_address").GetString());
        Assert.DoesNotContain(fixture.JudgeDllPath, fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void AdmissionSegmentRejectsMalformedJudgeBinaryAttestation()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);
        fixture.WriteMalformedJudgeAttestation();

        var result = fixture.RunAdmission();

        Assert.Equal(2, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(
            sentinel,
            "admission",
            2,
            "judge-address-verification-failed");
        Assert.DoesNotContain("gate:", fixture.RecordedCalls, StringComparison.Ordinal);
    }

    [Fact]
    public void JudgmentSegmentsRejectUnavailableAddressInputs()
    {
        if (OperatingSystem.IsWindows()) return;
        using var lean = new JudgmentSegmentFixture();
        using var admission = new JudgmentSegmentFixture();
        admission.WriteValidLeanEvidenceFixture();

        var leanResult = lean.RunLeanInspect(scribeSourceAddress: "not-an-address");
        var admissionResult = admission.RunAdmission(judgeSourceAddress: "not-an-address");

        Assert.Equal(2, leanResult.ExitCode);
        Assert.Equal(2, admissionResult.ExitCode);
        using var leanSentinel = AssertSingleSentinel(leanResult);
        using var admissionSentinel = AssertSingleSentinel(admissionResult);
        AssertCompleteSentinel(
            leanSentinel,
            "lean-inspect",
            2,
            "scribe-address-verification-failed");
        AssertCompleteSentinel(
            admissionSentinel,
            "admission",
            2,
            "judge-address-verification-failed");
    }

    [Fact]
    public void LeanInspectSegmentNormalizesUnexpectedScribeExit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();

        var result = fixture.RunLeanInspect(scribeExitCode: 9);

        Assert.Equal(2, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "lean-inspect", 2, "subprocess-infrastructure-failed");
    }

    [Fact]
    public void AdmissionSegmentNormalizesUnexpectedGateExit()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new JudgmentSegmentFixture();
        Assert.Equal(0, fixture.RunLeanInspect().ExitCode);

        var result = fixture.RunAdmission(gateExitCode: 9);

        Assert.Equal(2, result.ExitCode);
        using var sentinel = AssertSingleSentinel(result);
        AssertCompleteSentinel(sentinel, "admission", 2, "subprocess-infrastructure-failed");
    }

    [Fact]
    public void SegmentMakeTargetsPreserveRawClassWhenMakeFoldsFailures()
    {
        if (OperatingSystem.IsWindows()) return;
        using var candidate = new JudgmentSegmentFixture();
        using var infrastructure = new JudgmentSegmentFixture();

        var candidateResult = candidate.RunLeanInspect(scribeExitCode: 1, throughMake: true);
        var infrastructureResult = infrastructure.RunLeanInspect(scribeExitCode: 9, throughMake: true);

        Assert.Equal(2, candidateResult.ExitCode);
        Assert.Equal(2, infrastructureResult.ExitCode);
        using var candidateSentinel = AssertSingleSentinel(candidateResult);
        using var infrastructureSentinel = AssertSingleSentinel(infrastructureResult);
        AssertCompleteSentinel(candidateSentinel, "lean-inspect", 1, "candidate-check-failed");
        AssertCompleteSentinel(
            infrastructureSentinel,
            "lean-inspect",
            2,
            "subprocess-infrastructure-failed");
    }

    [Fact]
    public void JudgmentSegmentsMapInvalidEventIntoClosedOutcome()
    {
        if (OperatingSystem.IsWindows()) return;
        using var lean = new JudgmentSegmentFixture();
        using var admission = new JudgmentSegmentFixture();

        var leanResult = lean.RunLeanInspect(eventName: "bogus");
        var admissionResult = admission.RunAdmission(eventName: "bogus");

        Assert.Equal(2, leanResult.ExitCode);
        Assert.Equal(2, admissionResult.ExitCode);
        using var leanSentinel = AssertSingleSentinel(leanResult);
        using var admissionSentinel = AssertSingleSentinel(admissionResult);
        AssertCompleteSentinel(leanSentinel, "lean-inspect", 2, "missing-required-input");
        AssertCompleteSentinel(admissionSentinel, "admission", 2, "missing-required-input");
        Assert.Equal(JsonValueKind.Null, leanSentinel.RootElement.GetProperty("event").ValueKind);
        Assert.Equal(JsonValueKind.Null, admissionSentinel.RootElement.GetProperty("event").ValueKind);
    }

    [Fact]
    public void JudgmentSegmentsMapMissingEventToNull()
    {
        if (OperatingSystem.IsWindows()) return;
        using var lean = new JudgmentSegmentFixture();
        using var admission = new JudgmentSegmentFixture();

        var leanResult = lean.RunLeanInspect(eventName: null);
        var admissionResult = admission.RunAdmission(eventName: null);

        Assert.Equal(2, leanResult.ExitCode);
        Assert.Equal(2, admissionResult.ExitCode);
        using var leanSentinel = AssertSingleSentinel(leanResult);
        using var admissionSentinel = AssertSingleSentinel(admissionResult);
        AssertCompleteSentinel(leanSentinel, "lean-inspect", 2, "missing-required-input");
        AssertCompleteSentinel(admissionSentinel, "admission", 2, "missing-required-input");
        Assert.Equal(JsonValueKind.Null, leanSentinel.RootElement.GetProperty("event").ValueKind);
        Assert.Equal(JsonValueKind.Null, admissionSentinel.RootElement.GetProperty("event").ValueKind);
    }

    [Fact]
    public void JudgmentSegmentsSurviveMissingEvidenceLibraryWithClosedOutcome()
    {
        if (OperatingSystem.IsWindows()) return;
        using var lean = new JudgmentSegmentFixture();
        using var admission = new JudgmentSegmentFixture();
        admission.WriteValidLeanEvidenceFixture();
        lean.DeleteEvidenceLibrary();
        admission.DeleteEvidenceLibrary();

        var leanResult = lean.RunLeanInspect();
        var admissionResult = admission.RunAdmission();

        Assert.Equal(2, leanResult.ExitCode);
        Assert.Equal(2, admissionResult.ExitCode);
        using var leanSentinel = AssertSingleSentinel(leanResult);
        using var admissionSentinel = AssertSingleSentinel(admissionResult);
        AssertCompleteSentinel(
            leanSentinel,
            "lean-inspect",
            2,
            "subprocess-infrastructure-failed");
        AssertCompleteSentinel(
            admissionSentinel,
            "admission",
            2,
            "subprocess-infrastructure-failed");
    }

    private static JsonDocument AssertSingleSentinel(ProcessOutput result)
    {
        var output = Utf8(result.StandardOutput);
        var lines = output.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.True(lines.Length == 1, Diagnostics(result));
        Assert.DoesNotContain(": ", output, StringComparison.Ordinal);
        Assert.False(result.StandardOutput.AsSpan().StartsWith(new byte[] { 0xef, 0xbb, 0xbf }));
        return JsonDocument.Parse(lines[0]);
    }

    private static void AssertCompleteSentinel(
        JsonDocument sentinel,
        string segment,
        int rawRc,
        string outcome)
    {
        var root = sentinel.RootElement;
        Assert.Equal(EvidenceKeys, root.EnumerateObject().Select(static item => item.Name));
        Assert.Equal("pfci-segment-evidence-v1", root.GetProperty("schema_version").GetString());
        Assert.Equal(segment, root.GetProperty("segment").GetString());
        var eventValue = root.GetProperty("event");
        Assert.True(
            eventValue.ValueKind == JsonValueKind.Null
            || eventValue.ValueKind == JsonValueKind.String
                && eventValue.GetString() is "PR" or "push",
            $"unexpected segment event: {eventValue.GetRawText()}");
        Assert.Equal(rawRc, root.GetProperty("raw_rc").GetInt32());
        Assert.Equal(outcome, root.GetProperty("outcome").GetString());
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void AssertResolvedIdentity(
        JsonDocument sentinel,
        JudgmentSegmentFixture fixture)
    {
        var root = sentinel.RootElement;
        Assert.Equal(fixture.ExpectedMergeCommit, root.GetProperty("merge_commit").GetString());
        Assert.Equal(fixture.ExpectedTree, root.GetProperty("tree").GetString());
        Assert.Equal(fixture.ExpectedBase, root.GetProperty("base").GetString());
        if (fixture.ExpectedSourceHead is null)
        {
            Assert.Equal(JsonValueKind.Null, root.GetProperty("source_head").ValueKind);
        }
        else
        {
            Assert.Equal(fixture.ExpectedSourceHead, root.GetProperty("source_head").GetString());
        }
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Utf8(result.StandardOutput) + "\nstderr:\n" + Utf8(result.StandardError);

    private static string Utf8(byte[] bytes) => Encoding.UTF8.GetString(bytes);
}
