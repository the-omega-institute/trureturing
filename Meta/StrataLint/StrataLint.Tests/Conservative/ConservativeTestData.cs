using System.Collections.Immutable;
using StrataLint.Cli;

namespace StrataLint.Tests;

internal static class ConservativeTestData
{
    internal const string AdmitCase = "golden:admit-existing";
    internal const string RejectCase = "golden:reject-existing";
    internal const string BaseTreeCase = "actual:baseline-tree";
    internal const string CandidateTreeCase = "actual:candidate-tree";

    internal static ConservativeVerificationInput Input(
        Func<ImmutableArray<ConservativeCaseResult>, ImmutableArray<ConservativeCaseResult>>?
            mutateCandidate = null,
        ConservativeHarnessExecution? candidateExecution = null)
    {
        var baselineCases = Cases();
        var candidateCases = mutateCandidate is null
            ? baselineCases
            : mutateCandidate(baselineCases);
        return new ConservativeVerificationInput(
            BaselineCommitOid: GitOid('a'),
            BaselineTreeOid: GitOid('b'),
            CandidateCommitOid: GitOid('c'),
            CandidateTreeOid: GitOid('d'),
            BaselineHarnessRoot: Sha256('1'),
            CandidateHarnessRoot: Sha256('2'),
            BaselineLeanReportRoot: Sha256('3'),
            CandidateLeanReportRoot: Sha256('4'),
            CorpusRoot: Sha256('5'),
            CorpusCaseIds: [AdmitCase, RejectCase, BaseTreeCase],
            GoldenCaseCount: 2,
            BaseTreeCaseId: BaseTreeCase,
            CandidateTreeCaseId: CandidateTreeCase,
            BaselineExecution: new ConservativeHarnessExecution.Completed(new ConservativeHarnessRun(
                Sha256('1'),
                ["SL-001", "SL-022"],
                baselineCases)),
            CandidateExecution: candidateExecution
                ?? new ConservativeHarnessExecution.Completed(new ConservativeHarnessRun(
                    Sha256('2'),
                    ["SL-001", "SL-022"],
                    candidateCases)));
    }

    internal static ConservativeCaseResult WithDisposition(
        ConservativeCaseResult item,
        string caseId,
        ConservativeDisposition disposition,
        params string[] blockingRules) =>
        item.CaseId == caseId
            ? item with
            {
                Disposition = disposition,
                BlockingRules = blockingRules.ToImmutableArray(),
            }
            : item;

    private static ImmutableArray<ConservativeCaseResult> Cases() =>
    [
        Case(AdmitCase, ConservativeDisposition.Admit),
        Case(RejectCase, ConservativeDisposition.Block, ["SL-001"]),
        Case(BaseTreeCase, ConservativeDisposition.Admit),
        Case(
            CandidateTreeCase,
            ConservativeDisposition.Admit,
            ["SL-022"],
            [new ConservativeDiagnostic(
                "SL-022",
                "Meta/StrataLint/SyntheticProtected.cs",
                "meta change requires external human review")]),
    ];

    private static ConservativeCaseResult Case(
        string caseId,
        ConservativeDisposition disposition,
        ImmutableArray<string> blockingRules = default,
        ImmutableArray<ConservativeDiagnostic> sl022Diagnostics = default) =>
        new(
            caseId,
            Sha256(caseId[0]),
            disposition,
            blockingRules.IsDefault ? ImmutableArray<string>.Empty : blockingRules,
            sl022Diagnostics.IsDefault
                ? ImmutableArray<ConservativeDiagnostic>.Empty
                : sl022Diagnostics);

    private static string GitOid(char value) => new(value, 40);

    private static string Sha256(char value) => "sha256:" + new string(value, 64);
}
