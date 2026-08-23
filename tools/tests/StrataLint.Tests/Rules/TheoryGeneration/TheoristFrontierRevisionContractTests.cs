using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class TheoristFrontierContractTests
{
    [Fact]
    public void RetiredV2BaselineContractWithRevisionIsAcceptedByFullActiveCatalog()
    {
        var fixture = BaselineContractCarrier();
        fixture.AddRevisionToRetiredBaseline("weakening", caseId: "D5-T2803");
        fixture.RetireTheoristTarget();

        AssertFullActiveCatalogAccepts(fixture);
    }

    [Fact]
    public void RetiredBaselineWithMalformedRevisionIsRejectedByStatementIdentityRule()
    {
        var fixture = BaselineContractCarrier();
        fixture.AddRevisionToRetiredBaseline("strengthening", note: " ");
        fixture.RetireTheoristTarget();

        var diagnostic = Assert.Single(EvaluateDeliveryIdentity(fixture));

        Assert.Contains(
            "baseline Frontier revision.note must be non-empty",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RevisedFrontierStatementWithoutRevisionDeclarationIsRejectedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithoutRevision();

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build())).Capability;
        var diagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(27)));

        Assert.Contains(
            "changed exact_statement.statement_sha256 requires a revision declaration",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionPredecessorThatDoesNotEqualBaselineStatementIsRejectedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            predecessorSha256:
                "sha256:0000000000000000000000000000000000000000000000000000000000000000");

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build())).Capability;
        var diagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(27)));

        Assert.Contains(
            "revision.predecessor_sha256 must equal the baseline exact_statement.statement_sha256",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionKindOutsideTheClosedVocabularyIsRejectedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision("reinterpretation");

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build())).Capability;
        var diagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(27)));
        var contractDiagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(2)));

        Assert.Contains(
            "revision.kind must be one of equivalent-restatement, strengthening, weakening",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            "revision.kind must be one of equivalent-restatement, strengthening, weakening",
            contractDiagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void WeakeningRevisionWithoutCanonicalCaseIdIsRejectedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision("weakening");

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build())).Capability;
        var diagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(27)));

        Assert.Contains(
            "weakening revision.case_id must be a canonical case id",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("equivalent-restatement", null)]
    [InlineData("strengthening", null)]
    [InlineData("weakening", "D5-T2803")]
    public void LegalRevisionDeclarationIsAcceptedByFullActiveCatalog(
        string kind,
        string? caseId)
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(kind, caseId: caseId);

        AssertFullActiveCatalogAccepts(fixture);
    }

    [Fact]
    public void NewFrontierContractWithoutRevisionIsAcceptedByFullActiveCatalog()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget("prime-norm-irreducibility");

        AssertFullActiveCatalogAccepts(fixture);
    }

    [Fact]
    public void UnchangedHistoricalV2ContractWithoutRevisionIsAcceptedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();

        AssertFullActiveCatalogAccepts(fixture);
    }

    [Fact]
    public void RevisionWithBlankNoteIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision("strengthening", note: " ");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("revision.note must be non-empty", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionWithUnexpectedFieldIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision("strengthening");
        fixture.AddUnexpectedRevisionField();

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("revision keys are not canonical", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionWithNonCanonicalPredecessorShaIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            predecessorSha256: "sha256:ABC");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "revision.predecessor_sha256 must be a canonical sha256 address",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void WeakeningRevisionWithNonCanonicalCaseIdIsRejectedAsContract()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision("weakening", caseId: "2803");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "weakening revision.case_id must be a canonical case id",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    private static RuleFixture ExistingContractCarrier()
    {
        var fixture = new RuleFixture();
        fixture.AddHistoricalTheoristTarget(
            "prime-norm-irreducibility",
            baselineOwnerKind: "declaration-ready-mathematical-open",
            baselineIncludeContract: true);
        return fixture;
    }
}
