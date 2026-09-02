using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DuplicateDefinitionAdvisoryTests
{
    private const string DuplicateDefinitionMaterial =
        "statement-v1(uparams=[],type=ec(Fixture.DefType,[]),value=ec(Fixture.SharedValue,[]))";

    private const string DistinctDefinitionValueMaterial =
        "statement-v1(uparams=[],type=ec(Fixture.DefType,[]),value=ec(Fixture.OtherValue,[]))";

    [Theory]
    [InlineData("def")]
    [InlineData("opaque")]
    public void CandidateValueDeclarationRepeatingAnUntouchedDeclarationIsObserved(string kind)
    {
        var diagnostic = Assert.Single(Evaluate(CollidingCandidate(kind)));

        Assert.Equal(RuleId.CreateKnown(28), diagnostic.RuleId);
        Assert.Equal(RuleFixture.DuplicateRightGid + ".lean", diagnostic.Path);
        Assert.Contains("duplicate-definition", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            $"elaborated {kind} type-and-value material",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5.S1.Phase.DuplicateRight.candidateDefinition",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5.S0.Carrier.DuplicateLeft.existingDefinition",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Equal(DisplaySeverity.Warning, diagnostic.DisplaySeverity);
    }

    [Fact]
    public void SameDefinitionTypeWithDifferentValueIsSilent()
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.existingDefinition",
            DuplicateDefinitionMaterial,
            kind: "def");
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.candidateDefinition",
            DistinctDefinitionValueMaterial,
            kind: "def",
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Fact]
    public void IdenticalMaterialAcrossDifferentDeclarationKindsIsSilent()
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.existingDefinition",
            DuplicateDefinitionMaterial,
            kind: "def");
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.candidateDefinition",
            DuplicateDefinitionMaterial,
            kind: "opaque",
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Fact]
    public void PreexistingDefinitionCollisionInUntouchedModulesIsSilent()
    {
        var fixture = Pair(leftTouched: false, rightTouched: false, kind: "def");
        fixture.AddStatementModule(
            "D5/S3/Weil/TouchedElsewhere",
            "D5.S3.Weil.TouchedElsewhere.unrelated",
            RuleFixture.DistinctStatementType,
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Fact]
    public void DuplicateAcrossTwoTouchedDefinitionModulesIsObservedOnce()
    {
        var diagnostic = Assert.Single(Evaluate(
            Pair(leftTouched: true, rightTouched: true, kind: "def")));

        Assert.Equal(RuleFixture.DuplicateLeftGid + ".lean", diagnostic.Path);
        Assert.Contains("duplicate-definition", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DefinitionExcludedFromStatementIdentityIsOutsideTheAdvisory()
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.existingDefinition",
            DuplicateDefinitionMaterial,
            kind: "def");
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.candidateDefinition",
            DuplicateDefinitionMaterial,
            kind: "def",
            includeInStatement: false,
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Theory]
    [InlineData("casesOn")]
    [InlineData("recOn")]
    [InlineData("match_1_1")]
    [InlineData("match_1_8")]
    [InlineData("eq_1_2")]
    public void CompilerGeneratedValueDefinitionsAreOutsideTheAdvisory(string component)
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            $"D5.S0.Carrier.DuplicateLeft.GeneratedShape.{component}",
            DuplicateDefinitionMaterial,
            kind: "def");
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            $"D5.S1.Phase.DuplicateRight.GeneratedShape.{component}",
            DuplicateDefinitionMaterial,
            kind: "def",
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Theory]
    [InlineData("casesOnPurpose")]
    [InlineData("recOnPurpose")]
    [InlineData("match_cons")]
    [InlineData("match_1_tail")]
    [InlineData("eq_zero")]
    public void NearbyAuthoredDefinitionNamesRemainChecked(string component)
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            $"D5.S0.Carrier.DuplicateLeft.{component}",
            DuplicateDefinitionMaterial,
            kind: "def");
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            $"D5.S1.Phase.DuplicateRight.{component}",
            DuplicateDefinitionMaterial,
            kind: "def",
            touched: true);

        var diagnostic = Assert.Single(Evaluate(fixture));
        Assert.Contains("duplicate-definition", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CollidingDefinitionCandidateIsStillAdmittedUnderTheFullActiveCatalog()
    {
        var fixture = CollidingCandidate("def");
        fixture.AddDigestionCoverageTarget();

        var completed = Execute(fixture);

        var diagnostic = Assert.Single(completed.Diagnostics);
        Assert.Equal(RuleId.CreateKnown(28), diagnostic.RuleId);
        Assert.Contains("duplicate-definition", diagnostic.Message, StringComparison.Ordinal);
        Assert.Null(AdmissionEngine.RejectIfNeeded(
            completed,
            MetaEvaluationProfile.ForClear(Clear())));
    }

    private static RuleFixture CollidingCandidate(string kind)
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.existingDefinition",
            DuplicateDefinitionMaterial,
            kind: kind);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.candidateDefinition",
            DuplicateDefinitionMaterial,
            kind: kind,
            touched: true);
        return fixture;
    }

    private static RuleFixture Pair(bool leftTouched, bool rightTouched, string kind)
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.existingDefinition",
            DuplicateDefinitionMaterial,
            kind: kind,
            touched: leftTouched);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.candidateDefinition",
            DuplicateDefinitionMaterial,
            kind: kind,
            touched: rightTouched);
        return fixture;
    }

    private static ImmutableArray<Diagnostic> Evaluate(RuleFixture fixture) =>
        RuleCatalog.Default.EvaluateSingle(RuleId.CreateKnown(28), fixture.Build()).Diagnostics;

    private static CompletedRuleSet Execute(RuleFixture fixture) =>
        Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(fixture.Build())).Capability;

    private static MetaClear Clear() =>
        Assert.IsType<BootstrapOutcome.Clear>(
            BootstrapGate.Evaluate(RawChangeSet.Create([RuleFixture.BlueprintPath]))).Capability;
}
