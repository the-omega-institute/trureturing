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
        fixture.AddRevisionToRetiredBaseline(
            "strengthening",
            caseId: "D5-T2803",
            note: " ");
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
            "changed Frontier module blob requires a revision declaration",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionPredecessorBlobThatDoesNotEqualBaselineCarrierIsRejectedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            predecessorBlobOid:
                "git-sha1:0000000000000000000000000000000000000000",
            caseId: "D5-T2803");

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build())).Capability;
        var diagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(27)));

        Assert.Contains(
            "revision.predecessor_blob_oid must equal the baseline Frontier module Git blob OID",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionPredecessorStatementThatDoesNotEqualBaselineStatementIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            predecessorStatementSha256:
                "sha256:0000000000000000000000000000000000000000000000000000000000000000",
            caseId: "D5-T2803");

        var diagnostic = Assert.Single(EvaluateDeliveryIdentity(fixture));

        Assert.Contains(
            "revision.predecessor_statement_sha256 must equal the baseline exact_statement.statement_sha256",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionKindOutsideTheClosedVocabularyIsRejectedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "reinterpretation",
            caseId: "D5-T2803");

        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build())).Capability;
        var diagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(27)));
        var contractDiagnostic = Assert.Single(
            completed.Diagnostics.Where(static item => item.RuleId == RuleId.CreateKnown(2)));

        Assert.Contains(
            "revision.kind must be one of definition-refactor, equivalent-restatement, strengthening, weakening",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            "revision.kind must be one of definition-refactor, equivalent-restatement, strengthening, weakening",
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
    [InlineData("equivalent-restatement", "D5-T2803")]
    [InlineData("strengthening", "D5-T2803")]
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
    public void DefinitionRefactorWithUnchangedStatementIsAcceptedByFullActiveCatalog()
    {
        var fixture = ExistingContractCarrier();
        fixture.RefactorTheoristDefinitionWithRevision();

        AssertFullActiveCatalogAccepts(fixture);
    }

    [Fact]
    public void DefinitionRefactorCannotDescribeAChangedStatement()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision("definition-refactor");

        var diagnostic = Assert.Single(EvaluateDeliveryIdentity(fixture));

        Assert.Contains(
            "definition-refactor requires an unchanged exact_statement.statement_sha256",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void UnchangedStatementBlobChangeMustUseDefinitionRefactor()
    {
        var fixture = ExistingContractCarrier();
        fixture.RefactorTheoristDefinitionWithRevision(
            "strengthening",
            caseId: "D5-T2803");

        var diagnostic = Assert.Single(EvaluateDeliveryIdentity(fixture));

        Assert.Contains(
            "unchanged exact_statement.statement_sha256 requires revision.kind definition-refactor",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void UnverifiedStrengtheningWithoutCanonicalCaseIdIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision("strengthening");

        var diagnostics = Evaluate(fixture);

        Assert.Contains(diagnostics, diagnostic => diagnostic.Message.Contains(
            "strengthening revision.case_id must be a canonical case id",
            StringComparison.Ordinal));
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
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            caseId: "D5-T2803",
            note: " ");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("revision.note must be non-empty", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionWithUnexpectedFieldIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            caseId: "D5-T2803");
        fixture.AddUnexpectedRevisionField();

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains("revision keys are not canonical", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionWithNonCanonicalPredecessorBlobOidIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            predecessorBlobOid: "git-sha1:ABC",
            caseId: "D5-T2803");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "revision.predecessor_blob_oid must be a canonical Git blob OID",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void RevisionWithNonCanonicalPredecessorStatementShaIsRejected()
    {
        var fixture = ExistingContractCarrier();
        fixture.ReviseTheoristStatementWithRevision(
            "strengthening",
            predecessorStatementSha256: "sha256:ABC",
            caseId: "D5-T2803");

        var diagnostic = Assert.Single(Evaluate(fixture));

        Assert.Contains(
            "revision.predecessor_statement_sha256 must be a canonical sha256 address",
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
