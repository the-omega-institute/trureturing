using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class ContractEpochVerifierTests
{
    private const string RetiredPath = "Meta/StrataLint/Golden/values-kernels.toml";
    private const string ExtraPath = "Blueprint/D5/S0/Carrier/Ring.md";
    private const string LoaderPath = "Meta/ReplacementLoader.cs";
    private const string PlanId = "CONTRACT-VALID-001";
    private static readonly string TreeOid = "git-sha1:" + new string('a', 40);

    [Fact]
    public void CustodyTransferCoversAnExactRetiredPath()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([RetiredPath]);
        var custodian = new MachineCustodian(MachineCustodianKind.Loader, LoaderPath);
        var receipt = ContractEpochEvidenceReceipt.Custody(
            candidate.Root,
            [RetiredPath],
            custodian);
        var registration = Register(
            new TransitionPlan.CustodyTransferV1([RetiredPath], custodian, receipt.Reference),
            baseline,
            candidate);

        var result = Verify(
            baseline,
            candidate,
            [registration],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            ContractEpochEvidenceIndex.Create([receipt], [LoaderPath], []));

        Assert.True(result.Accepted);
        Assert.Empty(result.UncoveredObligations);
        Assert.Empty(result.Findings);
    }

    [Fact]
    public void AuthorityDischargeCoversAnExactRetiredRule()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithoutRuleObligation("SL-016");
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForRule(
            candidate.Root,
            "SL-016");
        var registration = Register(
            new TransitionPlan.AuthorityDischargeV1([], "SL-016", proof.Reference),
            baseline,
            candidate);

        var result = Verify(
            baseline,
            candidate,
            [registration],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            ContractEpochEvidenceIndex.Create([proof], [], []));

        Assert.True(result.Accepted);
        Assert.Empty(result.UncoveredObligations);
    }

    [Fact]
    public void ShrinkWithoutTransferOrDischargeLeavesAnUncoveredObligation()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([RetiredPath]);

        var result = Verify(baseline, candidate, [], [], ContractEpochEvidenceIndex.Empty);

        Assert.False(result.Accepted);
        Assert.Equal(["path:" + RetiredPath], result.UncoveredObligations.ToArray());
    }

    [Fact]
    public void PlanScopeOutsideTheComputedDeltaIsRejected()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([RetiredPath]);
        var custodian = new MachineCustodian(MachineCustodianKind.Loader, LoaderPath);
        var receipt = ContractEpochEvidenceReceipt.Custody(
            candidate.Root,
            [RetiredPath, ExtraPath],
            custodian);
        var registration = Register(
            new TransitionPlan.CustodyTransferV1(
                [RetiredPath, ExtraPath],
                custodian,
                receipt.Reference),
            baseline,
            candidate);

        var result = Verify(
            baseline,
            candidate,
            [registration],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            ContractEpochEvidenceIndex.Create([receipt], [LoaderPath], []));

        Assert.False(result.Accepted);
        Assert.Contains(result.Findings, item => item.Code == "CONTRACT-EPOCH-SCOPE-OUTSIDE-DELTA");
        Assert.Equal(["path:" + RetiredPath], result.UncoveredObligations.ToArray());
    }

    [Fact]
    public void MissingMachineCustodianInvalidatesTheTransfer()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([RetiredPath]);
        var custodian = new MachineCustodian(MachineCustodianKind.Loader, LoaderPath);
        var receipt = ContractEpochEvidenceReceipt.Custody(
            candidate.Root,
            [RetiredPath],
            custodian);
        var registration = Register(
            new TransitionPlan.CustodyTransferV1([RetiredPath], custodian, receipt.Reference),
            baseline,
            candidate);

        var result = Verify(
            baseline,
            candidate,
            [registration],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            ContractEpochEvidenceIndex.Create([receipt], [], []));

        Assert.False(result.Accepted);
        Assert.Contains(result.Findings, item => item.Code == "CONTRACT-EPOCH-CUSTODIAN-INVALID");
        Assert.Equal(["path:" + RetiredPath], result.UncoveredObligations.ToArray());
    }

    [Fact]
    public void ContractEpochCannotRetireItsOwnVerifierSurface()
    {
        const string unshrinkable =
            "Meta/StrataLint/StrataLint.Cli/Conservative/ContractEpoch/TransitionPlan.cs";
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([unshrinkable]);
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
            candidate.Root,
            [unshrinkable]);
        var registration = Register(
            new TransitionPlan.AuthorityDischargeV1([unshrinkable], null, proof.Reference),
            baseline,
            candidate);

        var result = Verify(
            baseline,
            candidate,
            [registration],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            ContractEpochEvidenceIndex.Create([proof], [], []));

        Assert.False(result.Accepted);
        Assert.Contains(result.Findings, item => item.Code == "CONTRACT-EPOCH-UNSHRINKABLE");
        Assert.Equal(["path:" + unshrinkable], result.UncoveredObligations.ToArray());
    }

    [Fact]
    public void CandidateAddedPlanCannotAuthorizeItsOwnShrink()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([RetiredPath]);
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
            candidate.Root,
            [RetiredPath]);
        var registration = Register(
            new TransitionPlan.AuthorityDischargeV1([RetiredPath], null, proof.Reference),
            baseline,
            candidate);

        var result = Verify(
            baseline,
            candidate,
            [],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            ContractEpochEvidenceIndex.Create([proof], [], []));

        Assert.False(result.Accepted);
        Assert.Contains(
            result.Findings,
            item => item.Code == "CONTRACT-EPOCH-CANDIDATE-PLAN-INELIGIBLE");
        Assert.Equal(["path:" + RetiredPath], result.UncoveredObligations.ToArray());
    }

    [Fact]
    public void CandidateEvidenceValidatesANewRegistrationWithoutGrantingAuthority()
    {
        var policy = ConservativePolicySnapshot.Current();
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
            policy.Root,
            [RetiredPath]);
        var registration = Register(
            new TransitionPlan.AuthorityDischargeV1([RetiredPath], null, proof.Reference),
            policy,
            policy);

        var result = Verify(
            policy,
            policy,
            [],
            [registration],
            ContractEpochEvidenceIndex.Empty,
            ContractEpochEvidenceIndex.Create([proof], [], []));

        Assert.True(result.Accepted);
        Assert.Empty(result.Findings);
    }

    [Fact]
    public void CandidateEvidenceCannotAuthorizeConsumptionOfABasePlan()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([RetiredPath]);
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
            candidate.Root,
            [RetiredPath]);
        var registration = Register(
            new TransitionPlan.AuthorityDischargeV1([RetiredPath], null, proof.Reference),
            baseline,
            candidate);

        var result = Verify(
            baseline,
            candidate,
            [registration],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            ContractEpochEvidenceIndex.Empty,
            ContractEpochEvidenceIndex.Create([proof], [], []));

        Assert.False(result.Accepted);
        Assert.Contains(result.Findings, item => item.Code == "CONTRACT-EPOCH-EVIDENCE-INVALID");
        Assert.Equal(["path:" + RetiredPath], result.UncoveredObligations.ToArray());
    }

    [Fact]
    public void ConsumptionTrustsAPlanValidatedInAnEarlierBaseTree()
    {
        var baseline = BeforeResidenceEpoch();
        var candidate = baseline.WithExactExclusions([RetiredPath]);
        var proof = ContractEpochEvidenceReceipt.UnreachabilityForPaths(
            candidate.Root,
            [RetiredPath]);
        var registration = new ContractEpochEvent.Register(
            PlanId,
            "git-sha1:" + new string('b', 40),
            baseline.Root,
            candidate.Root,
            new TransitionPlan.AuthorityDischargeV1(
                [RetiredPath],
                null,
                proof.Reference));
        var evidence = ContractEpochEvidenceIndex.Create([proof], [], []);

        var result = Verify(
            baseline,
            candidate,
            [registration],
            [registration, new ContractEpochEvent.Consume(PlanId)],
            evidence,
            evidence);

        Assert.True(result.Accepted);
        Assert.DoesNotContain(result.Findings, item => item.Code == "CONTRACT-EPOCH-ROOT-DRIFT");
    }

    private static ContractEpochEvent.Register Register(
        TransitionPlan plan,
        ConservativePolicySnapshot baseline,
        ConservativePolicySnapshot candidate) => new(
        PlanId,
        TreeOid,
        baseline.Root,
        candidate.Root,
        plan);

    private static ContractEpochComparisonResult Verify(
        ConservativePolicySnapshot baseline,
        ConservativePolicySnapshot candidate,
        IEnumerable<ContractEpochEvent> baselineEvents,
        IEnumerable<ContractEpochEvent> candidateEvents,
        ContractEpochEvidenceIndex evidence) => Verify(
            baseline,
            candidate,
            baselineEvents,
            candidateEvents,
            evidence,
            evidence);

    private static ContractEpochComparisonResult Verify(
        ConservativePolicySnapshot baseline,
        ConservativePolicySnapshot candidate,
        IEnumerable<ContractEpochEvent> baselineEvents,
        IEnumerable<ContractEpochEvent> candidateEvents,
        ContractEpochEvidenceIndex baselineEvidence,
        ContractEpochEvidenceIndex candidateEvidence) => ContractEpochVerifier.Verify(new(
        TreeOid,
        baseline,
        candidate,
        ContractEpochLedgerCodec.Read(ContractEpochLedgerCodec.Write(baselineEvents).AsSpan()),
        ContractEpochLedgerCodec.Read(ContractEpochLedgerCodec.Write(candidateEvents).AsSpan()),
        baselineEvidence,
        candidateEvidence));

    private static ConservativePolicySnapshot BeforeResidenceEpoch() =>
        ConservativePolicySnapshot.Current().WithExactExclusions([]);
}
