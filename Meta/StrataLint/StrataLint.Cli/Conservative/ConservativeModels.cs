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
    ImmutableArray<ConservativeCaseResult> Cases)
{
    internal ConservativePolicySnapshot Policy { get; init; } =
        ConservativePolicySnapshot.Current().WithRuleObligations(ActiveRules);

    internal ImmutableArray<ConservativeContractCaseResult> ContractCases { get; init; } = [];
}

internal sealed record ConservativeContractCaseResult(
    string CaseId,
    ImmutableArray<string> FindingCodes);

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
    string ReplayRoot,
    ImmutableArray<string> CorpusCaseIds,
    int GoldenCaseCount,
    string BaseTreeCaseId,
    string CandidateTreeCaseId,
    ConservativeHarnessExecution BaselineExecution,
    ConservativeHarnessExecution CandidateExecution)
{
    internal ContractEpochLedger BaselineContractLedger { get; init; } = ContractEpochLedger.Empty;

    internal ContractEpochLedger CandidateContractLedger { get; init; } = ContractEpochLedger.Empty;

    internal ContractEpochEvidenceIndex BaselineContractEvidence { get; init; } =
        ContractEpochEvidenceIndex.Empty;

    internal ContractEpochEvidenceIndex CandidateContractEvidence { get; init; } =
        ContractEpochEvidenceIndex.Empty;

    internal ImmutableDictionary<string, ImmutableArray<string>> ContractExpectations { get; init; } =
        ImmutableDictionary<string, ImmutableArray<string>>.Empty.WithComparers(StringComparer.Ordinal);
}

internal sealed record ConservativeFinding(
    string Code,
    string? CaseId,
    string? RuleId,
    string Message)
{
    internal string? Obligation { get; init; }
}

internal abstract record ConservativeExtensionOutcome
{
    private ConservativeExtensionOutcome() { }

    internal sealed record Accepted(ImmutableArray<byte> Certificate) : ConservativeExtensionOutcome;

    internal sealed record Violated(
        ImmutableArray<byte> Certificate,
        ImmutableArray<ConservativeFinding> Findings) : ConservativeExtensionOutcome;

    internal sealed record InfrastructureFailure(string Message) : ConservativeExtensionOutcome;
}
