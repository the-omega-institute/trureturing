using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class EngineeringTestExecutionHarnessScriptTests
{
    [Fact]
    public void EngineeringSegmentSuccessEmitsOneCompleteCanonicalJsonLine()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario());

        Assert.Equal(0, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        var root = sentinel.RootElement;
        Assert.Equal(
        [
            "schema_version", "segment", "event", "merge_commit", "tree", "base",
            "source_head", "raw_rc", "outcome", "report_input_address", "report_sha256",
            "judge_source_address", "scribe_source_address", "selected_test_ids",
            "ordered_check_ids",
        ],
            root.EnumerateObject().Select(static property => property.Name));
        Assert.Equal("pfci-segment-evidence-v1", root.GetProperty("schema_version").GetString());
        Assert.Equal("engineering", root.GetProperty("segment").GetString());
        Assert.Equal("push", root.GetProperty("event").GetString());
        Assert.Equal(0, root.GetProperty("raw_rc").GetInt32());
        Assert.Equal("passed", root.GetProperty("outcome").GetString());
        Assert.Equal(JsonValueKind.Null, root.GetProperty("source_head").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("report_input_address").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("report_sha256").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("judge_source_address").ValueKind);
        Assert.Equal(JsonValueKind.Null, root.GetProperty("scribe_source_address").ValueKind);
        Assert.Equal(
        [
            "Alpha.Tests::Class.Quote\"Case",
            "Zeta.Tests::Class.Path\\Case",
        ],
            root.GetProperty("selected_test_ids").EnumerateArray()
                .Select(static value => value.GetString()));
        Assert.Equal(
        [
            "restore-compile-fail-proofs",
            "restore-engineering-solution",
            "build-candidate",
            "engineering-tests",
            "stratalint-selftest",
            "compile-fail-proof",
            "banned-api-compile-fail-proof",
        ],
            root.GetProperty("ordered_check_ids").EnumerateArray()
                .Select(static value => value.GetString()));
        Assert.DoesNotContain(": ", run.StandardOutput, StringComparison.Ordinal);
        Assert.False(
            run.Process.StandardOutput.Length >= 3
            && run.Process.StandardOutput.AsSpan(0, 3).SequenceEqual(
                new byte[] { 0xef, 0xbb, 0xbf }));
    }

    [Fact]
    public void EngineeringSegmentKeepsRawClassesWhenMakeFoldsFailuresToTwo()
    {
        if (OperatingSystem.IsWindows()) return;
        using var candidateDirect = RunSegment(new SegmentScenario(
            EngineeringExitCode: 1,
            EmitEngineeringEvidenceOnFailure: true));
        using var candidateMake = RunSegment(new SegmentScenario(
            EngineeringExitCode: 1,
            EmitEngineeringEvidenceOnFailure: true,
            InvokeThroughMake: true));
        using var infrastructureDirect = RunSegment(new SegmentScenario(BuildExitCode: 9));
        using var infrastructureMake = RunSegment(new SegmentScenario(
            BuildExitCode: 9,
            InvokeThroughMake: true));

        Assert.Equal(1, candidateDirect.Process.ExitCode);
        Assert.Equal(2, candidateMake.Process.ExitCode);
        Assert.Equal(2, infrastructureDirect.Process.ExitCode);
        Assert.Equal(2, infrastructureMake.Process.ExitCode);
        AssertSentinel(candidateDirect, 1, "candidate-check-failed");
        AssertSentinel(candidateMake, 1, "candidate-check-failed");
        AssertSentinel(infrastructureDirect, 2, "subprocess-infrastructure-failed");
        AssertSentinel(infrastructureMake, 2, "subprocess-infrastructure-failed");
    }

    [Fact]
    public void EngineeringSegmentExitOneWithoutTrxIdentityEvidenceIsInfrastructure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EngineeringExitCode: 1));

        Assert.Equal(2, run.Process.ExitCode);
        AssertSentinel(run, 2, "subprocess-infrastructure-failed");
    }

    [Fact]
    public void EngineeringSegmentFailureAfterSelectionPreservesExecutedIdentities()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(
            EngineeringExitCode: 1,
            EmitEngineeringEvidenceOnFailure: true));

        Assert.Equal(1, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal(
        [
            "Alpha.Tests::Class.Quote\"Case",
            "Zeta.Tests::Class.Path\\Case",
        ],
            sentinel.RootElement.GetProperty("selected_test_ids").EnumerateArray()
                .Select(static value => value.GetString()));
    }

    [Fact]
    public void EngineeringSegmentPlanWithoutIdentityKeepsSelectionNull()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EmitEngineeringPlanOnly: true));

        Assert.Equal(0, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentEncodesIdentityPayloadLargerThanMaxArgStrlen()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EmitLargeEngineeringEvidence: true));

        Assert.Equal(0, run.Process.ExitCode);
        Assert.True(run.Process.StandardOutput.Length > 300 * 1024, run.Diagnostics);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        var identities = sentinel.RootElement.GetProperty("selected_test_ids").EnumerateArray()
            .Select(static value => value.GetString()).ToArray();
        Assert.Equal(5000, identities.Length);
        Assert.Equal("Owner0000.Tests::Namespace.Class.Method0000_" + new string('x', 48), identities[0]);
        Assert.Equal("Owner4999.Tests::Namespace.Class.Method4999_" + new string('x', 48), identities[^1]);
    }

    [Fact]
    public void EngineeringSegmentMissingEvidenceLibraryStillEmitsCompleteSentinel()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(MissingEvidenceLibrary: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        Assert.Equal("evidence-library-unavailable", sentinel.RootElement.GetProperty("outcome").GetString());
    }

    [Fact]
    public void EngineeringSegmentMalformedIdentityStillEmitsCompleteSentinel()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(EmitMalformedEngineeringEvidence: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentRecordCheckEncodingFailureStillEmitsCompleteSentinel()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(RecordCheckEncodingFails: true));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        AssertCompleteSentinel(sentinel);
        Assert.Equal(JsonValueKind.Array, sentinel.RootElement.GetProperty("ordered_check_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentInvalidEventFailsBeforeEvidenceSelection()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(Event: "invalid\"event\\value"));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal("invalid\"event\\value", sentinel.RootElement.GetProperty("event").GetString());
        Assert.Equal(2, sentinel.RootElement.GetProperty("raw_rc").GetInt32());
        Assert.Equal("invalid-event", sentinel.RootElement.GetProperty("outcome").GetString());
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("merge_commit").ValueKind);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentPrRequiresExactlyTwoParents()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(Event: "PR"));

        Assert.Equal(2, run.Process.ExitCode);
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal("parent-mismatch", sentinel.RootElement.GetProperty("outcome").GetString());
        Assert.Equal(2, sentinel.RootElement.GetProperty("raw_rc").GetInt32());
        Assert.Matches("^[0-9a-f]{40}$", sentinel.RootElement.GetProperty("merge_commit").GetString());
        Assert.Matches("^[0-9a-f]{40}$", sentinel.RootElement.GetProperty("tree").GetString());
        Assert.Matches("^[0-9a-f]{40}$", sentinel.RootElement.GetProperty("base").GetString());
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("source_head").ValueKind);
        Assert.Equal(JsonValueKind.Null, sentinel.RootElement.GetProperty("selected_test_ids").ValueKind);
    }

    [Fact]
    public void EngineeringSegmentCompileFailProofRequiresBothStrongMarkers()
    {
        if (OperatingSystem.IsWindows()) return;
        using var missingCode = RunSegment(new SegmentScenario(IncludeCs7036: false));
        using var missingCapability = RunSegment(new SegmentScenario(IncludeMetaClear: false));

        Assert.Equal(1, missingCode.Process.ExitCode);
        Assert.Equal(1, missingCapability.Process.ExitCode);
        AssertSentinel(missingCode, 1, "candidate-check-failed");
        AssertSentinel(missingCapability, 1, "candidate-check-failed");
    }

    [Fact]
    public void EngineeringSegmentCompileFailProofExitOneInfrastructureIsRawTwo()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(CompileFailInfrastructureError: true));

        Assert.Equal(2, run.Process.ExitCode);
        AssertSentinel(run, 2, "subprocess-infrastructure-failed");
    }

    [Fact]
    public void EngineeringSegmentBannedApiProofExitOneInfrastructureIsRawTwo()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSegment(new SegmentScenario(BannedApiInfrastructureError: true));

        Assert.Equal(2, run.Process.ExitCode);
        AssertSentinel(run, 2, "subprocess-infrastructure-failed");
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void SelftestDotnetExitOneIsInfrastructureForEitherRun(int failingRun)
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSelftest(failingRun, mismatch: false);

        Assert.Equal(2, run.Process.ExitCode);
    }

    [Fact]
    public void SelftestByteMismatchIsCandidateFailure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunSelftest(failingRun: 0, mismatch: true);

        Assert.Equal(1, run.Process.ExitCode);
    }

    private static void AssertSentinel(SegmentRun run, int rawRc, string outcome)
    {
        using var sentinel = AssertSingleSentinel(run);
        Assert.Equal(rawRc, sentinel.RootElement.GetProperty("raw_rc").GetInt32());
        Assert.Equal(outcome, sentinel.RootElement.GetProperty("outcome").GetString());
    }

    private static JsonDocument AssertSingleSentinel(SegmentRun run)
    {
        var lines = run.StandardOutput.Split('\n', StringSplitOptions.RemoveEmptyEntries);
        Assert.True(lines.Length == 1, run.Diagnostics);
        return JsonDocument.Parse(lines[0]);
    }

    private static void AssertCompleteSentinel(JsonDocument sentinel) =>
        Assert.Equal(
        [
            "schema_version", "segment", "event", "merge_commit", "tree", "base",
            "source_head", "raw_rc", "outcome", "report_input_address", "report_sha256",
            "judge_source_address", "scribe_source_address", "selected_test_ids",
            "ordered_check_ids",
        ],
            sentinel.RootElement.EnumerateObject().Select(static property => property.Name));

    private sealed record SegmentScenario(
        string Event = "push",
        int BuildExitCode = 0,
        int EngineeringExitCode = 0,
        int SelftestExitCode = 0,
        bool EmitEngineeringEvidenceOnFailure = false,
        bool EmitEngineeringPlanOnly = false,
        bool EmitMalformedEngineeringEvidence = false,
        bool EmitLargeEngineeringEvidence = false,
        bool IncludeCs7036 = true,
        bool IncludeMetaClear = true,
        bool InvokeThroughMake = false,
        bool MissingEvidenceLibrary = false,
        bool RecordCheckEncodingFails = false,
        bool CompileFailInfrastructureError = false,
        bool BannedApiInfrastructureError = false);

    private sealed record SegmentRun(
        TemporaryDirectory Temporary,
        ProcessOutput Process) : IDisposable
    {
        internal string Diagnostics => ProcessDiagnostics(Process);

        internal string StandardOutput => Utf8.GetString(Process.StandardOutput);

        public void Dispose() => Temporary.Dispose();
    }
}
