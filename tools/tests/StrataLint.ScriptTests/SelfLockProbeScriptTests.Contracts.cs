namespace StrataLint.Tests;

public sealed partial class SelfLockProbeScriptTests
{
    private sealed record ProbeResult(
        int SchemaVersion,
        string Decision,
        ProbeAuthorization Authorization,
        string[] ReasonCodes,
        ProbeJudgment[] Judgments);

    private sealed record ProbeAuthorization(
        bool AllowExactRevert,
        bool ChangesGateStatus,
        bool RerunRequiredAfterDevPush,
        string[] ConfirmedRedGates);

    private sealed record ProbeJudgment(
        string Gate,
        string Subject,
        string Outcome,
        string[] ReasonCodes);

    private sealed record PublishedBundle(
        string AuthorityReceiptPath,
        string PayloadPath);

    private static string CompleteTrx(IReadOnlyList<string> tests)
    {
        var results = string.Join(
            string.Empty,
            tests.Select(test => $"<UnitTestResult testName=\"{test}\" outcome=\"Passed\" />"));
        return $"""
            <?xml version="1.0" encoding="utf-8"?>
            <TestRun xmlns="http://microsoft.com/schemas/VisualStudio/TeamTest/2010">
              <Results>{results}</Results>
              <ResultSummary outcome="Completed"><Counters total="{tests.Count}" executed="{tests.Count}" passed="{tests.Count}" failed="0" error="0" timeout="0" aborted="0" inconclusive="0" notExecuted="0" /></ResultSummary>
            </TestRun>
            """;
    }

    private static string DigestFile(string path) => DigestScratchFile(path);
}
