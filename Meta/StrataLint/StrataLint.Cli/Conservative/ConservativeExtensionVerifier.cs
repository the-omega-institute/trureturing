using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class ConservativeExtensionVerifier
{
    private const string CertificateSchema = "stratalint-conservative-certificate-v1";

    internal static ConservativeExtensionOutcome Verify(ConservativeVerificationInput input)
    {
        ArgumentNullException.ThrowIfNull(input);
        if (input.BaselineExecution is ConservativeHarnessExecution.InfrastructureFailure baselineFailure)
        {
            return new ConservativeExtensionOutcome.InfrastructureFailure(
                $"baseline harness infrastructure failure: {baselineFailure.Message}");
        }

        if (input.CandidateExecution is ConservativeHarnessExecution.InfrastructureFailure candidateFailure)
        {
            return new ConservativeExtensionOutcome.InfrastructureFailure(
                $"candidate harness infrastructure failure: {candidateFailure.Message}");
        }

        var baseline = ((ConservativeHarnessExecution.Completed)input.BaselineExecution).Run;
        var candidate = ((ConservativeHarnessExecution.Completed)input.CandidateExecution).Run;
        try
        {
            ValidateRoot("baseline", input.BaselineHarnessRoot, baseline.HarnessRoot);
            ValidateRoot("candidate", input.CandidateHarnessRoot, candidate.HarnessRoot);
            var expectedIds = ExpectedCaseIds(input);
            var baselineById = ValidateCases("baseline", baseline.Cases, expectedIds);
            var candidateById = ValidateCases("candidate", candidate.Cases, expectedIds);
            foreach (var caseId in expectedIds)
            {
                if (!string.Equals(
                    baselineById[caseId].CaseRoot,
                    candidateById[caseId].CaseRoot,
                    StringComparison.Ordinal))
                {
                    throw new InvalidOperationException(
                        $"case root mismatch for {caseId}: the two harnesses did not consume the same input");
                }
            }

            var activeRules = ValidateActiveRules(baseline.ActiveRules);
            var findings = Compare(
                input,
                activeRules,
                baselineById,
                candidateById);
            var certificate = WriteCertificate(
                input,
                baseline,
                candidate,
                activeRules,
                baselineById,
                candidateById,
                findings);
            return findings.IsEmpty
                ? new ConservativeExtensionOutcome.Accepted(certificate)
                : new ConservativeExtensionOutcome.Violated(certificate, findings);
        }
        catch (InvalidOperationException exception)
        {
            return new ConservativeExtensionOutcome.InfrastructureFailure(exception.Message);
        }
    }

    private static ImmutableArray<string> ExpectedCaseIds(ConservativeVerificationInput input)
    {
        if (input.CorpusCaseIds.IsDefaultOrEmpty
            || input.GoldenCaseCount < 1
            || input.GoldenCaseCount >= input.CorpusCaseIds.Length
            || !input.CorpusCaseIds.Contains(input.BaseTreeCaseId, StringComparer.Ordinal)
            || input.CorpusCaseIds.Contains(input.CandidateTreeCaseId, StringComparer.Ordinal))
        {
            throw new InvalidOperationException("conservative corpus case set is invalid");
        }

        return input.CorpusCaseIds.Add(input.CandidateTreeCaseId);
    }

    private static ImmutableDictionary<string, ConservativeCaseResult> ValidateCases(
        string side,
        ImmutableArray<ConservativeCaseResult> cases,
        ImmutableArray<string> expectedIds)
    {
        if (cases.IsDefault)
        {
            throw new InvalidOperationException($"{side} harness case set is missing");
        }

        var expected = expectedIds.Order(StringComparer.Ordinal).ToArray();
        var actual = cases.Select(static item => item.CaseId).Order(StringComparer.Ordinal).ToArray();
        if (!actual.SequenceEqual(expected, StringComparer.Ordinal)
            || actual.Distinct(StringComparer.Ordinal).Count() != actual.Length)
        {
            throw new InvalidOperationException(
                $"{side} harness case set does not exactly match the base-owned corpus");
        }

        if (cases.Any(static item => string.IsNullOrWhiteSpace(item.CaseRoot)
            || item.BlockingRules.IsDefault
            || item.Sl022Diagnostics.IsDefault))
        {
            throw new InvalidOperationException($"{side} harness emitted an incomplete case result");
        }

        return cases.ToImmutableDictionary(static item => item.CaseId, StringComparer.Ordinal);
    }

    private static ImmutableArray<string> ValidateActiveRules(ImmutableArray<string> rules)
    {
        if (rules.IsDefaultOrEmpty
            || rules.Any(static rule => string.IsNullOrWhiteSpace(rule))
            || rules.Distinct(StringComparer.Ordinal).Count() != rules.Length)
        {
            throw new InvalidOperationException("baseline active rule set is missing or malformed");
        }

        return rules.Order(StringComparer.Ordinal).ToImmutableArray();
    }

    private static ImmutableArray<ConservativeFinding> Compare(
        ConservativeVerificationInput input,
        ImmutableArray<string> activeRules,
        ImmutableDictionary<string, ConservativeCaseResult> baseline,
        ImmutableDictionary<string, ConservativeCaseResult> candidate)
    {
        var findings = ImmutableArray.CreateBuilder<ConservativeFinding>();
        var baselineTree = baseline[input.BaseTreeCaseId];
        if (baselineTree.Disposition is not ConservativeDisposition.Admit)
        {
            throw new InvalidOperationException(
                "baseline harness no longer admits its own actual tree; blocking_rules="
                + string.Join(',', baselineTree.BlockingRules));
        }

        foreach (var caseId in input.CorpusCaseIds)
        {
            if (baseline[caseId].Disposition is ConservativeDisposition.Admit
                && candidate[caseId].Disposition is not ConservativeDisposition.Admit)
            {
                findings.Add(new ConservativeFinding(
                    "CONSERVATIVE-ADMIT-FLIPPED",
                    caseId,
                    null,
                    "candidate harness rejected a case admitted by the baseline harness"));
            }
        }

        if (baseline[input.CandidateTreeCaseId].Disposition is not ConservativeDisposition.Admit)
        {
            findings.Add(new ConservativeFinding(
                "CONSERVATIVE-ACTUAL-BASELINE-BLOCKED",
                input.CandidateTreeCaseId,
                null,
                "baseline harness did not provisionally admit the actual candidate tree"));
        }

        if (candidate[input.CandidateTreeCaseId].Disposition is not ConservativeDisposition.Admit)
        {
            findings.Add(new ConservativeFinding(
                "CONSERVATIVE-ACTUAL-CANDIDATE-BLOCKED",
                input.CandidateTreeCaseId,
                null,
                "candidate harness did not provisionally admit the actual candidate tree"));
        }

        foreach (var ruleId in activeRules)
        {
            var witnessCases = input.CorpusCaseIds
                .Take(input.GoldenCaseCount)
                .Where(caseId =>
                    baseline[caseId].Disposition is ConservativeDisposition.Block
                    && baseline[caseId].BlockingRules.Contains(ruleId, StringComparer.Ordinal))
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (witnessCases.Length == 0)
            {
                throw new InvalidOperationException(
                    $"base-owned corpus has no blocking witness for active rule {ruleId}");
            }

            if (!witnessCases.Any(caseId =>
                candidate[caseId].Disposition is ConservativeDisposition.Block
                && candidate[caseId].BlockingRules.Contains(ruleId, StringComparer.Ordinal)))
            {
                findings.Add(new ConservativeFinding(
                    "CONSERVATIVE-BLOCK-WITNESS-LOST",
                    null,
                    ruleId,
                    "candidate harness lost every base-owned blocking witness for the active rule"));
            }
        }

        var baselineProtectedPaths = baseline[input.CandidateTreeCaseId].Sl022Diagnostics
            .Select(static item => item.Path)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (baselineProtectedPaths.Length == 0)
        {
            throw new InvalidOperationException("actual meta case has no baseline SL-022 diagnostics");
        }

        var candidateProtectedPaths = candidate[input.CandidateTreeCaseId].Sl022Diagnostics
            .Select(static item => item.Path)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var path in baselineProtectedPaths.Where(path => !candidateProtectedPaths.Contains(path)))
        {
            findings.Add(new ConservativeFinding(
                "CONSERVATIVE-SL022-PROTECTION-LOST",
                input.CandidateTreeCaseId,
                "SL-022",
                $"candidate harness no longer classifies protected path {path}"));
        }

        return findings
            .OrderBy(static item => item.Code, StringComparer.Ordinal)
            .ThenBy(static item => item.CaseId, StringComparer.Ordinal)
            .ThenBy(static item => item.RuleId, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static ImmutableArray<byte> WriteCertificate(
        ConservativeVerificationInput input,
        ConservativeHarnessRun baselineRun,
        ConservativeHarnessRun candidateRun,
        ImmutableArray<string> activeRules,
        ImmutableDictionary<string, ConservativeCaseResult> baseline,
        ImmutableDictionary<string, ConservativeCaseResult> candidate,
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
                harness_root = input.BaselineHarnessRoot,
                lean_report_root = input.BaselineLeanReportRoot,
                result_root = HarnessResultRoot(baselineRun),
                tree_oid = input.BaselineTreeOid,
            },
            candidate = new
            {
                commit_oid = input.CandidateCommitOid,
                harness_root = input.CandidateHarnessRoot,
                lean_report_root = input.CandidateLeanReportRoot,
                result_root = HarnessResultRoot(candidateRun),
                tree_oid = input.CandidateTreeOid,
            },
            corpus_case_count = input.CorpusCaseIds.Length,
            corpus_root = input.CorpusRoot,
            findings = findings.Select(static item => new
            {
                case_id = item.CaseId,
                code = item.Code,
                message = item.Message,
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
            harness_root = run.HarnessRoot,
        });
        var bytes = StructuredCanonicalWriter.WriteJson(material);
        return "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes.AsSpan()));
    }

    private static void ValidateRoot(string side, string expected, string actual)
    {
        if (!string.Equals(expected, actual, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"{side} harness root does not match the executed program set");
        }
    }
}
