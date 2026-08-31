using System.Text.Json.Nodes;

namespace StrataLint.Tests;

public sealed partial class SelfLockProbeScriptTests
{
    private const string ShutdownDiagnostic = """
        MSBUILD : error MSB4166: Child node "N" exited prematurely. Shutting down.
        make: *** [Makefile:23: engineering-tests] Error 143
        ##[error]The runner has received a shutdown signal.
        ##[error]The operation was canceled.
        """;

    [Theory]
    [InlineData("shutdown-1")]
    [InlineData("shutdown-2")]
    [InlineData("shutdown-3")]
    public void RunnerShutdownIsInfrastructureAndIndeterminate(string signal)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J1Bundle.Supervisor["termination"] = new JsonObject
        {
            ["kind"] = "signal",
            ["exit_code"] = null,
            ["signal"] = signal,
        };
        fixture.J1Bundle.Supervisor["diagnostics"] = new JsonArray(ShutdownDiagnostic);
        fixture.J1Bundle.Supervisor["step_failures"] = new JsonArray();
        fixture.J1Bundle.Publish();

        var output = RunProbe(fixture, ["engineering"], ["engineering"]);

        AssertDecision(
            output,
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
        Assert.Contains(
            ParseResult(output).Judgments,
            judgment => judgment.Subject == "j1" && judgment.Outcome == "infrastructure_failure");
    }

    [Theory]
    [InlineData("j1")]
    [InlineData("j0")]
    public void MissingFinalizationSentinelIsIndeterminate(string subject)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        (subject == "j1" ? fixture.J1Bundle : fixture.J0Bundle).RemoveFinalizationSentinel();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Theory]
    [InlineData("j1")]
    [InlineData("j0")]
    public void IncompleteDiagnosticsAreIndeterminate(string subject)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        var bundle = subject == "j1" ? fixture.J1Bundle : fixture.J0Bundle;
        bundle.Supervisor["diagnostics_complete"] = false;
        bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("partial")]
    [InlineData("zero")]
    public void MissingPartialOrZeroExecutionTrxIsIndeterminate(string shape)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        if (shape == "missing")
        {
            fixture.J0Bundle.RemoveTrxFile();
        }
        else if (shape == "partial")
        {
            fixture.J0Bundle.TrxText = CompleteTrx([PresentTest]).Replace(
                "total=\"1\" executed=\"1\" passed=\"1\"",
                "total=\"2\" executed=\"2\" passed=\"2\"",
                StringComparison.Ordinal);
            fixture.J0Bundle.Publish();
        }
        else
        {
            fixture.J0Bundle.TrxText = CompleteTrx([]);
            fixture.J0Bundle.Publish();
        }

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void StaleOrSubstitutedTrxArtifactIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.CorruptTrxWithoutRebinding();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void MarkerTextWithoutPolicyArtifactIsInfrastructure()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J1Bundle.Supervisor["failure_keys"] = new JsonArray();
        fixture.J1Bundle.Supervisor["blockers"] = new JsonArray();
        fixture.J1Bundle.Supervisor["diagnostics"] = new JsonArray(
            "ENGINEERING_TEST_EVIDENCE_FAILED missing=Engineering.Tests.RequiredIdentity");
        fixture.J1Bundle.Publish();

        var output = RunProbe(fixture, ["engineering"], ["engineering"]);

        AssertDecision(
            output,
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
        Assert.Contains(
            ParseResult(output).Judgments,
            judgment => judgment.Subject == "j1" && judgment.Outcome == "infrastructure_failure");
    }

    [Fact]
    public void DifferentEvaluatorDigestsAreIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        fixture.J0Bundle.Supervisor["evaluator_digest"] = "sha256:" + new string('b', 64);
        fixture.J0Bundle.Publish();

        AssertDecision(
            RunProbe(fixture, ["engineering"], ["engineering"]),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void MalformedPureRevertConclusionIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        var classifier = fixture.WriteExecutable(
            "malformed-classifier.sh",
            "printf '%s\\n' 'PURE_REVERT_TRUE malformed'\nexit 0");

        AssertDecision(
            RunControllerWithClassifier(fixture, classifier),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }

    [Fact]
    public void MalformedNegativePureRevertConclusionIsIndeterminate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ProbeFixture();
        var classifier = fixture.WriteExecutable(
            "malformed-negative-classifier.sh",
            "printf '%s\\n' 'NOT_A_PURE_REVERT_CONCLUSION' >&2\nexit 5");

        AssertDecision(
            RunControllerWithClassifier(fixture, classifier),
            "PROBE_INDETERMINATE",
            allowExactRevert: false,
            exitCode: 2);
    }
}
