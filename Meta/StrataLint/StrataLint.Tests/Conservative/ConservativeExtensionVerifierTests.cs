using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ConservativeExtensionVerifierTests
{
    [Fact]
    public void ConservativeChangePreservesAdmitsAndEveryBlockingWitness()
    {
        var outcome = ConservativeExtensionVerifier.Verify(ConservativeTestData.Input());

        var accepted = Assert.IsType<ConservativeExtensionOutcome.Accepted>(outcome);
        var certificate = Encoding.UTF8.GetString(accepted.Certificate.AsSpan());
        Assert.Contains("\"status\": \"CORPUS_CONSERVATIVE\"", certificate, StringComparison.Ordinal);
        Assert.Contains("\"corpus_case_count\": 4", certificate, StringComparison.Ordinal);
        Assert.Contains("\"golden_case_count\": 3", certificate, StringComparison.Ordinal);
        Assert.Contains("\"replay_root\": \"sha256:", certificate, StringComparison.Ordinal);
        Assert.Contains("\"SL-022\"", certificate, StringComparison.Ordinal);
        Assert.Contains("\"policy_root\": \"sha256:", certificate, StringComparison.Ordinal);
        Assert.Contains("\"uncovered_obligations\": []", certificate, StringComparison.Ordinal);
    }

    [Fact]
    public void PolicyShrinkIsRejectedWithoutActualChangedPathInference()
    {
        const string retired = "Meta/StrataLint/Golden/values-kernels.toml";
        var input = ConservativeTestData.Input();
        var candidate = Assert.IsType<ConservativeHarnessExecution.Completed>(
            input.CandidateExecution);
        input = input with
        {
            CandidateExecution = new ConservativeHarnessExecution.Completed(candidate.Run with
            {
                Policy = candidate.Run.Policy.WithExactExclusions([retired]),
            }),
        };

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            item => item.Code == "CONTRACT-EPOCH-UNCOVERED-OBLIGATION");
        Assert.DoesNotContain(
            violated.Findings,
            item => item.Code == "CONSERVATIVE-SL022-PROTECTION-LOST");
    }

    [Fact]
    public void CandidateAddedDeclarationCannotAuthorizeTheCurrentComparison()
    {
        const string retired = "Meta/StrataLint/Golden/values-kernels.toml";
        const string planId = "CONTRACT-SAME-PR-001";
        var input = ConservativeTestData.Input();
        var baseline = Assert.IsType<ConservativeHarnessExecution.Completed>(
            input.BaselineExecution).Run.Policy;
        var candidateExecution = Assert.IsType<ConservativeHarnessExecution.Completed>(
            input.CandidateExecution);
        var candidate = candidateExecution.Run.Policy.WithExactExclusions([retired]);
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(candidate.Root, [retired]);
        var registration = new ContractEpochEvent.Register(
            planId,
            input.BaselineTreeOid,
            baseline.Root,
            candidate.Root,
            new TransitionPlan.AuthorityDischargeV1([retired], null, proof.Reference));
        input = input with
        {
            CandidateExecution = new ConservativeHarnessExecution.Completed(candidateExecution.Run with
            {
                Policy = candidate,
            }),
            CandidateContractLedger = ContractEpochLedgerCodec.Read(
                ContractEpochLedgerCodec.Write(
                    [registration, new ContractEpochEvent.Consume(planId)]).AsSpan()),
            CandidateContractEvidence = ContractEpochEvidenceIndex.Create([proof], [], []),
        };

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            item => item.Code == "CONTRACT-EPOCH-CANDIDATE-PLAN-INELIGIBLE");
        Assert.Contains(
            violated.Findings,
            item => item.Code == "CONTRACT-EPOCH-UNCOVERED-OBLIGATION");
    }

    [Fact]
    public void FlippingAnOldAdmitIsAContractViolation()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.AdmitCase,
                ConservativeDisposition.Block,
                "SL-001"))
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            finding => finding.Code == "CONSERVATIVE-ADMIT-FLIPPED"
                && finding.CaseId == ConservativeTestData.AdmitCase);
    }

    [Fact]
    public void RemovingAnActiveRuleBlockingWitnessIsDetectionDegradation()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.RejectCase,
                ConservativeDisposition.Admit))
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            finding => finding.Code == "CONSERVATIVE-BLOCK-WITNESS-LOST"
                && finding.RuleId == "SL-001");
    }

    [Fact]
    public void AdmitDispositionCannotRetainARuleIdToFakeABlockingWitness()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.RejectCase,
                ConservativeDisposition.Admit,
                "SL-001"))
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var violated = Assert.IsType<ConservativeExtensionOutcome.Violated>(outcome);
        Assert.Contains(
            violated.Findings,
            finding => finding.Code == "CONSERVATIVE-BLOCK-WITNESS-LOST"
                && finding.RuleId == "SL-001");
    }

    [Fact]
    public void CoveredExactPathRetirementCanLoseItsOldSl022Diagnostic()
    {
        const string retired = "Meta/StrataLint/Golden/values-kernels.toml";
        const string planId = "CONTRACT-PATH-P2-001";
        var input = ConservativeTestData.Input();
        var baselineExecution = Assert.IsType<ConservativeHarnessExecution.Completed>(
            input.BaselineExecution);
        var candidateExecution = Assert.IsType<ConservativeHarnessExecution.Completed>(
            input.CandidateExecution);
        var baselinePolicy = baselineExecution.Run.Policy;
        var candidatePolicy = candidateExecution.Run.Policy.WithExactExclusions([retired]);
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
            candidatePolicy.Root,
            [retired]);
        var registration = new ContractEpochEvent.Register(
            planId,
            input.BaselineTreeOid,
            baselinePolicy.Root,
            candidatePolicy.Root,
            new TransitionPlan.AuthorityDischargeV1([retired], null, proof.Reference));
        var baselineCases = WithCandidateTreeDiagnostics(
            baselineExecution.Run.Cases,
            [new ConservativeDiagnostic(
                "SL-022",
                retired,
                "meta change requires external human review")]);
        var candidateCases = WithCandidateTreeDiagnostics(candidateExecution.Run.Cases, []);
        var evidence = ContractEpochEvidenceIndex.Create([proof], [], []);
        input = input with
        {
            BaselineExecution = new ConservativeHarnessExecution.Completed(
                baselineExecution.Run with { Cases = baselineCases }),
            CandidateExecution = new ConservativeHarnessExecution.Completed(candidateExecution.Run with
            {
                Cases = candidateCases,
                Policy = candidatePolicy,
            }),
            BaselineContractLedger = Ledger([registration]),
            CandidateContractLedger = Ledger(
                [registration, new ContractEpochEvent.Consume(planId)]),
            BaselineContractEvidence = evidence,
            CandidateContractEvidence = evidence,
        };

        var outcome = ConservativeExtensionVerifier.Verify(input);

        Assert.IsType<ConservativeExtensionOutcome.Accepted>(outcome);
    }

    [Fact]
    public void CoveredRuleRetirementLeavesOnlyNonretiredRulesOnTheNegativeFloor()
    {
        const string planId = "CONTRACT-RULE-P2-001";
        var input = ConservativeTestData.Input();
        var baselineExecution = Assert.IsType<ConservativeHarnessExecution.Completed>(
            input.BaselineExecution);
        var candidateExecution = Assert.IsType<ConservativeHarnessExecution.Completed>(
            input.CandidateExecution);
        var baselinePolicy = baselineExecution.Run.Policy;
        var candidatePolicy = candidateExecution.Run.Policy.WithoutRuleObligation("SL-001");
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForRule(
            candidatePolicy.Root,
            "SL-001");
        var registration = new ContractEpochEvent.Register(
            planId,
            input.BaselineTreeOid,
            baselinePolicy.Root,
            candidatePolicy.Root,
            new TransitionPlan.AuthorityDischargeV1([], "SL-001", proof.Reference));
        var candidateCases = candidateExecution.Run.Cases
            .Select(item => ConservativeTestData.WithDisposition(
                item,
                ConservativeTestData.RejectCase,
                ConservativeDisposition.Admit))
            .ToImmutableArray();
        var evidence = ContractEpochEvidenceIndex.Create([proof], [], []);
        input = input with
        {
            CandidateExecution = new ConservativeHarnessExecution.Completed(candidateExecution.Run with
            {
                ActiveRules = ["SL-022"],
                Cases = candidateCases,
                Policy = candidatePolicy,
            }),
            BaselineContractLedger = Ledger([registration]),
            CandidateContractLedger = Ledger(
                [registration, new ContractEpochEvent.Consume(planId)]),
            BaselineContractEvidence = evidence,
            CandidateContractEvidence = evidence,
        };

        var accepted = Assert.IsType<ConservativeExtensionOutcome.Accepted>(
            ConservativeExtensionVerifier.Verify(input));
        var certificate = Encoding.UTF8.GetString(accepted.Certificate.AsSpan());

        Assert.Contains("\"active_rule_count\": 1", certificate, StringComparison.Ordinal);
        Assert.Contains("\"rules\": [\"SL-022\"]", certificate, StringComparison.Ordinal);
    }

    [Fact]
    public void MissingCandidateCaseIsInfrastructureFailure()
    {
        var input = ConservativeTestData.Input(cases => cases
            .Where(item => item.CaseId != ConservativeTestData.RejectCase)
            .ToImmutableArray());

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var failure = Assert.IsType<ConservativeExtensionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("case set", failure.Message, StringComparison.OrdinalIgnoreCase);
    }

    [Fact]
    public void HarnessTimeoutIsInfrastructureFailure()
    {
        var input = ConservativeTestData.Input(
            candidateExecution: new ConservativeHarnessExecution.InfrastructureFailure(
                "candidate harness timed out"));

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var failure = Assert.IsType<ConservativeExtensionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("timed out", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void BaselineTreeIntegrityFailureNamesTheBlockingRules()
    {
        var input = ConservativeTestData.Input() with
        {
            BaselineExecution = new ConservativeHarnessExecution.Completed(new ConservativeHarnessRun(
                "sha256:" + new string('1', 64),
                ["SL-001", "SL-022"],
                Assert.IsType<ConservativeHarnessExecution.Completed>(
                        ConservativeTestData.Input().BaselineExecution)
                    .Run.Cases
                    .Select(item => ConservativeTestData.WithDisposition(
                        item,
                        ConservativeTestData.BaseTreeCase,
                        ConservativeDisposition.Block,
                        "SL-001"))
                    .ToImmutableArray())),
        };

        var outcome = ConservativeExtensionVerifier.Verify(input);

        var failure = Assert.IsType<ConservativeExtensionOutcome.InfrastructureFailure>(outcome);
        Assert.Contains("SL-001", failure.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CertificateBytesAreStableAcrossRuns()
    {
        var input = ConservativeTestData.Input();

        var first = Assert.IsType<ConservativeExtensionOutcome.Accepted>(
            ConservativeExtensionVerifier.Verify(input));
        var second = Assert.IsType<ConservativeExtensionOutcome.Accepted>(
            ConservativeExtensionVerifier.Verify(input));

        Assert.True(first.Certificate.AsSpan().SequenceEqual(second.Certificate.AsSpan()));
    }

    private static ContractEpochLedger Ledger(IEnumerable<ContractEpochEvent> events) =>
        ContractEpochLedgerCodec.Read(ContractEpochLedgerCodec.Write(events).AsSpan());

    private static ImmutableArray<ConservativeCaseResult> WithCandidateTreeDiagnostics(
        ImmutableArray<ConservativeCaseResult> cases,
        ImmutableArray<ConservativeDiagnostic> diagnostics) => cases.Select(item =>
            item.CaseId == ConservativeTestData.CandidateTreeCase
                ? item with
                {
                    BlockingRules = diagnostics.IsEmpty ? [] : ["SL-022"],
                    Sl022Diagnostics = diagnostics,
                }
                : item).ToImmutableArray();
}
