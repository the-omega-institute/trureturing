using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class ConservativeExtensionVerifier
{
    internal const string CertificateSchema = "stratalint-conservative-certificate-v1";

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

            var baselineActiveRules = ValidateActiveRules("baseline", baseline);
            _ = ValidateActiveRules("candidate", candidate);
            var contract = ContractEpochVerifier.Verify(new ContractEpochComparisonInput(
                input.BaselineTreeOid,
                baseline.Policy,
                candidate.Policy,
                input.BaselineContractLedger,
                input.CandidateContractLedger,
                input.BaselineContractEvidence,
                input.CandidateContractEvidence));
            var retiredPaths = contract.Accepted
                ? contract.PolicyDelta.RetiredExactPaths.ToImmutableHashSet(StringComparer.Ordinal)
                : ImmutableHashSet<string>.Empty.WithComparer(StringComparer.Ordinal);
            var activeRules = contract.Accepted
                ? baselineActiveRules.Where(rule => !contract.PolicyDelta.RetiredRuleObligations
                        .Contains(rule, StringComparer.Ordinal))
                    .ToImmutableArray()
                : baselineActiveRules;
            var findings = Compare(
                input,
                activeRules,
                retiredPaths,
                baselineById,
                candidateById).ToBuilder();
            ValidateContractCorpus(input, baseline, candidate, findings);
            findings.AddRange(contract.Findings.Select(static item => new ConservativeFinding(
                item.Code,
                null,
                null,
                item.Message)
            {
                Obligation = item.Subject,
            }));
            var orderedFindings = OrderFindings(findings);
            var certificate = WriteCertificate(
                input,
                baseline,
                candidate,
                activeRules,
                baselineById,
                candidateById,
                contract,
                orderedFindings);
            return orderedFindings.IsEmpty
                ? new ConservativeExtensionOutcome.Accepted(certificate)
                : new ConservativeExtensionOutcome.Violated(certificate, orderedFindings);
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

    private static ImmutableArray<string> ValidateActiveRules(
        string side,
        ConservativeHarnessRun run)
    {
        var rules = run.ActiveRules;
        if (rules.IsDefaultOrEmpty
            || rules.Any(static rule => string.IsNullOrWhiteSpace(rule))
            || rules.Distinct(StringComparer.Ordinal).Count() != rules.Length)
        {
            throw new InvalidOperationException($"{side} active rule set is missing or malformed");
        }

        var ordered = rules.Order(StringComparer.Ordinal).ToImmutableArray();
        var policyRules = run.Policy.RuleObligations
            .Select(static item => item.RuleId)
            .Order(StringComparer.Ordinal)
            .ToArray();
        if (!ordered.SequenceEqual(policyRules, StringComparer.Ordinal))
        {
            throw new InvalidOperationException(
                $"{side} active rules do not equal the canonical policy obligations");
        }

        return ordered;
    }

    private static ImmutableArray<ConservativeFinding> Compare(
        ConservativeVerificationInput input,
        ImmutableArray<string> activeRules,
        ImmutableHashSet<string> retiredExactPaths,
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
        var candidateProtectedPaths = candidate[input.CandidateTreeCaseId].Sl022Diagnostics
            .Select(static item => item.Path)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var path in baselineProtectedPaths.Where(path =>
            !candidateProtectedPaths.Contains(path) && !retiredExactPaths.Contains(path)))
        {
            findings.Add(new ConservativeFinding(
                "CONSERVATIVE-SL022-PROTECTION-LOST",
                input.CandidateTreeCaseId,
                "SL-022",
                $"candidate harness no longer classifies protected path {path}"));
        }

        return OrderFindings(findings);
    }

    private static void ValidateContractCorpus(
        ConservativeVerificationInput input,
        ConservativeHarnessRun baseline,
        ConservativeHarnessRun candidate,
        ImmutableArray<ConservativeFinding>.Builder findings)
    {
        var expectedIds = input.ContractExpectations.Keys.Order(StringComparer.Ordinal).ToArray();
        var baselineIds = baseline.ContractCases.Select(static item => item.CaseId)
            .Order(StringComparer.Ordinal).ToArray();
        if (!baselineIds.SequenceEqual(expectedIds, StringComparer.Ordinal)
            || baselineIds.Distinct(StringComparer.Ordinal).Count() != baselineIds.Length)
        {
            throw new InvalidOperationException(
                "baseline contract corpus result set does not equal the base-owned expectations");
        }

        foreach (var result in baseline.ContractCases)
        {
            if (!result.FindingCodes.SequenceEqual(
                input.ContractExpectations[result.CaseId],
                StringComparer.Ordinal))
            {
                throw new InvalidOperationException(
                    $"baseline contract corpus result disagrees with expectation: {result.CaseId}");
            }
        }

        var candidateById = candidate.ContractCases
            .ToDictionary(static item => item.CaseId, StringComparer.Ordinal);
        foreach (var (caseId, expected) in input.ContractExpectations)
        {
            if (!candidateById.TryGetValue(caseId, out var actual)
                || !actual.FindingCodes.SequenceEqual(expected, StringComparer.Ordinal))
            {
                findings.Add(new ConservativeFinding(
                    "CONTRACT-EPOCH-CORPUS-REGRESSION",
                    caseId,
                    null,
                    "candidate harness no longer rejects the base-owned contract epoch attack case"));
            }
        }

        foreach (var extra in candidateById.Keys.Where(id => !input.ContractExpectations.ContainsKey(id)))
        {
            findings.Add(new ConservativeFinding(
                "CONTRACT-EPOCH-CORPUS-REGRESSION",
                extra,
                null,
                "candidate harness emitted a contract corpus result outside the base-owned case set"));
        }
    }

    private static ImmutableArray<ConservativeFinding> OrderFindings(
        IEnumerable<ConservativeFinding> findings) => findings
            .OrderBy(static item => item.Code, StringComparer.Ordinal)
            .ThenBy(static item => item.CaseId, StringComparer.Ordinal)
            .ThenBy(static item => item.RuleId, StringComparer.Ordinal)
            .ThenBy(static item => item.Obligation, StringComparer.Ordinal)
            .ThenBy(static item => item.Message, StringComparer.Ordinal)
            .ToImmutableArray();

    private static void ValidateRoot(string side, string expected, string actual)
    {
        if (!string.Equals(expected, actual, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"{side} harness root does not match the executed program set");
        }
    }
}
