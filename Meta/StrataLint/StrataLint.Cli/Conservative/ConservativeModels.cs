using System.Collections.Immutable;

namespace StrataLint.Cli;

internal enum ConservativeDisposition
{
    Admit,
    Block,
}

internal sealed record ConservativeDiagnostic(string RuleId, string Path, string Message);

internal sealed record ConservativeCaseResult(
    string CaseId,
    string CaseRoot,
    ConservativeDisposition Disposition,
    ImmutableArray<string> BlockingRules,
    ImmutableArray<ConservativeDiagnostic> Sl022Diagnostics);

internal sealed record ConservativeHarnessRun(
    string HarnessRoot,
    ImmutableArray<string> ActiveRules,
    ImmutableArray<ConservativeCaseResult> Cases);

internal abstract record ConservativeHarnessExecution
{
    private ConservativeHarnessExecution() { }

    internal sealed record Completed(ConservativeHarnessRun Run) : ConservativeHarnessExecution;

    internal sealed record InfrastructureFailure(string Message) : ConservativeHarnessExecution;
}

internal sealed record ConservativeVerificationInput(
    string BaselineCommitOid,
    string BaselineTreeOid,
    string CandidateCommitOid,
    string CandidateTreeOid,
    string BaselineHarnessRoot,
    string CandidateHarnessRoot,
    string BaselineLeanReportRoot,
    string CandidateLeanReportRoot,
    string CorpusRoot,
    ImmutableArray<string> CorpusCaseIds,
    int GoldenCaseCount,
    string BaseTreeCaseId,
    string CandidateTreeCaseId,
    ConservativeHarnessExecution BaselineExecution,
    ConservativeHarnessExecution CandidateExecution);

internal sealed record ConservativeFinding(
    string Code,
    string? CaseId,
    string? RuleId,
    string Message);

internal abstract record ConservativeExtensionOutcome
{
    private ConservativeExtensionOutcome() { }

    internal sealed record Accepted(ImmutableArray<byte> Certificate) : ConservativeExtensionOutcome;

    internal sealed record Violated(
        ImmutableArray<byte> Certificate,
        ImmutableArray<ConservativeFinding> Findings) : ConservativeExtensionOutcome;

    internal sealed record InfrastructureFailure(string Message) : ConservativeExtensionOutcome;
}
