using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class ConservativeExtensionVerifier
{
    private static ImmutableArray<byte> WriteCertificate(
        ConservativeVerificationInput input,
        ConservativeHarnessRun baselineRun,
        ConservativeHarnessRun candidateRun,
        ImmutableArray<string> activeRules,
        ImmutableDictionary<string, ConservativeCaseResult> baseline,
        ImmutableDictionary<string, ConservativeCaseResult> candidate,
        ContractEpochComparisonResult contract,
        ImmutableArray<ConservativeFinding> findings)
    {
        var baselineAdmits = input.CorpusCaseIds.Count(caseId =>
            baseline[caseId].Disposition is ConservativeDisposition.Admit);
        var preservedAdmits = input.CorpusCaseIds.Count(caseId =>
            baseline[caseId].Disposition is ConservativeDisposition.Admit
            && candidate[caseId].Disposition is ConservativeDisposition.Admit);
        var material = JsonSerializer.SerializeToElement(new
        {
            actual_candidate_case = new
            {
                baseline = Disposition(baseline[input.CandidateTreeCaseId]),
                candidate = Disposition(candidate[input.CandidateTreeCaseId]),
                case_id = input.CandidateTreeCaseId,
            },
            actual_tree_case = new
            {
                baseline = Disposition(baseline[input.BaseTreeCaseId]),
                candidate = Disposition(candidate[input.BaseTreeCaseId]),
                case_id = input.BaseTreeCaseId,
            },
            baseline = new
            {
                commit_oid = input.BaselineCommitOid,
                contract_ledger_root = input.BaselineContractLedger.Root,
                harness_root = input.BaselineHarnessRoot,
                lean_report_root = input.BaselineLeanReportRoot,
                policy_root = baselineRun.Policy.Root,
                result_root = HarnessResultRoot(baselineRun),
                tree_oid = input.BaselineTreeOid,
            },
            candidate = new
            {
                commit_oid = input.CandidateCommitOid,
                contract_ledger_root = input.CandidateContractLedger.Root,
                harness_root = input.CandidateHarnessRoot,
                lean_report_root = input.CandidateLeanReportRoot,
                policy_root = candidateRun.Policy.Root,
                result_root = HarnessResultRoot(candidateRun),
                tree_oid = input.CandidateTreeOid,
            },
            contract_epoch = new
            {
                contract_case_count = input.ContractExpectations.Count,
                retired_exact_paths = contract.PolicyDelta.RetiredExactPaths,
                retired_rule_obligations = contract.PolicyDelta.RetiredRuleObligations,
                uncovered_obligations = contract.UncoveredObligations,
            },
            corpus_case_count = input.CorpusCaseIds.Length,
            corpus_root = input.CorpusRoot,
            findings = findings.Select(static item => new
            {
                case_id = item.CaseId,
                code = item.Code,
                message = item.Message,
                obligation = item.Obligation,
                rule_id = item.RuleId,
            }),
            golden_case_count = input.GoldenCaseCount,
            negative_floor = new
            {
                active_rule_count = activeRules.Length,
                rules = activeRules,
            },
            positive_implication = new
            {
                baseline_admit_count = baselineAdmits,
                preserved_admit_count = preservedAdmits,
            },
            replay_root = input.ReplayRoot,
            schema = CertificateSchema,
            sl022_diagnostics = new
            {
                baseline = Diagnostics(baseline[input.CandidateTreeCaseId]),
                candidate = Diagnostics(candidate[input.CandidateTreeCaseId]),
            },
            status = findings.IsEmpty ? "CORPUS_CONSERVATIVE" : "CONSERVATIVE_VIOLATION",
        });
        return StructuredCanonicalWriter.WriteJson(material);
    }

    private static object Disposition(ConservativeCaseResult result) => new
    {
        blocking_rules = result.BlockingRules.Order(StringComparer.Ordinal),
        disposition = result.Disposition.ToString().ToLowerInvariant(),
    };

    private static IEnumerable<object> Diagnostics(ConservativeCaseResult result) =>
        result.Sl022Diagnostics
            .OrderBy(static item => item.Path, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .Select(static item => (object)new
            {
                message = item.Message,
                path = item.Path,
                rule_id = item.RuleId,
            });

    private static string HarnessResultRoot(ConservativeHarnessRun run)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            active_rules = run.ActiveRules.Order(StringComparer.Ordinal),
            cases = run.Cases.OrderBy(static item => item.CaseId, StringComparer.Ordinal).Select(item => new
            {
                blocking_rules = item.BlockingRules.Order(StringComparer.Ordinal),
                case_id = item.CaseId,
                case_root = item.CaseRoot,
                disposition = item.Disposition.ToString().ToLowerInvariant(),
                sl022_diagnostics = Diagnostics(item),
            }),
            contract_cases = run.ContractCases.OrderBy(static item => item.CaseId, StringComparer.Ordinal)
                .Select(static item => new
                {
                    case_id = item.CaseId,
                    finding_codes = item.FindingCodes,
                }),
            harness_root = run.HarnessRoot,
            policy_root = run.Policy.Root,
        });
        var bytes = StructuredCanonicalWriter.WriteJson(material);
        return "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes.AsSpan()));
    }
}
