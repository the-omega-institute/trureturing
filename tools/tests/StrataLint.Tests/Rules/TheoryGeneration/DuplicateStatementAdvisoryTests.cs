using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DuplicateStatementAdvisoryTests
{
    // Names Lean generates. Each entry is the clause of the closed marker
    // vocabulary it pins: dropping that clause makes this case report.
    public static TheoryData<string> GeneratedNames => new()
    {
        "D5.S1.Phase.DuplicateRight._simp_1",
        "D5.S1.Phase.DuplicateRight._proof_2",
        "_private.D5.S1.Phase.DuplicateRight.0.dup",
        "D5.S1.Phase.DuplicateRight.eq_1",
        "D5.S1.Phase.DuplicateRight.eq_def",
        "D5.S1.Phase.DuplicateRight.match_1",
        "D5.S1.Phase.DuplicateRight.congr_simp",
        "D5.S1.Phase.DuplicateRight.instIsTransNatLeHAddOfNat_d5",
    };

    // Names a human writes that resemble the generated ones above. Widening any
    // marker clause to cover these turns the advisory silent on real duplicates,
    // which is the failure this rule exists to prevent.
    public static TheoryData<string> HumanNamesResemblingGeneratedOnes => new()
    {
        "D5.S1.Phase.DuplicateRight.simp_lemma",
        "D5.S1.Phase.DuplicateRight.proof_irrel",
        "D5.S1.Phase.DuplicateRight.private_core",
        "D5.S1.Phase.DuplicateRight.eq_zero",
        "D5.S1.Phase.DuplicateRight.eq_def_of_lt",
        "D5.S1.Phase.DuplicateRight.match_cons",
        "D5.S1.Phase.DuplicateRight.congr_simp_of_eq",
        "D5.S1.Phase.DuplicateRight.instability_bound",
        "D5.S1.Phase.DuplicateRight.instΔLemma",
    };

    [Fact]
    public void CandidateTheoremRepeatingAnUntouchedModulesStatementIsObserved()
    {
        var diagnostic = Assert.Single(Evaluate(CollidingCandidate()));

        Assert.Equal(RuleId.CreateKnown(28), diagnostic.RuleId);
        Assert.Equal(RuleFixture.DuplicateRightGid + ".lean", diagnostic.Path);
    }

    [Fact]
    public void ObservedDuplicateNamesBothDeclarations()
    {
        var diagnostic = Assert.Single(Evaluate(CollidingCandidate()));

        Assert.Contains("duplicate-statement", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains(
            "D5.S1.Phase.DuplicateRight.dpi_defect",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5.S0.Carrier.DuplicateLeft.channel_monotone",
            diagnostic.Message,
            StringComparison.Ordinal);
        Assert.Contains(
            RuleFixture.DuplicateLeftGid + ".lean",
            diagnostic.Message,
            StringComparison.Ordinal);
    }

    [Fact]
    public void DuplicateStatementNeverBlocksAdmission()
    {
        var diagnostic = Assert.Single(Evaluate(CollidingCandidate()));

        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Equal(DisplaySeverity.Warning, diagnostic.DisplaySeverity);
    }

    [Fact]
    public void CollidingCandidateIsStillAdmittedUnderTheFullActiveCatalog()
    {
        var fixture = CollidingCandidate();
        fixture.AddDigestionCoverageTarget();

        var completed = Execute(fixture);

        var diagnostic = Assert.Single(completed.Diagnostics);
        Assert.Equal(RuleId.CreateKnown(28), diagnostic.RuleId);
        Assert.Null(AdmissionEngine.RejectIfNeeded(
            completed,
            MetaEvaluationProfile.ForClear(Clear())));
    }

    [Fact]
    public void PreexistingDuplicateInUntouchedModulesIsSilent()
    {
        var fixture = Pair(leftTouched: false, rightTouched: false);
        fixture.AddStatementModule(
            "D5/S3/Weil/TouchedElsewhere",
            "D5.S3.Weil.TouchedElsewhere.unrelated",
            RuleFixture.DistinctStatementType,
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Fact]
    public void PreexistingDuplicateFixtureIsLawfulUnderTheFullActiveCatalog()
    {
        var fixture = Pair(leftTouched: false, rightTouched: false);
        fixture.AddDigestionCoverageTarget();

        var completed = Execute(fixture);

        Assert.Empty(completed.Diagnostics);
        var active = RuleCatalog.Default.Descriptors
            .Where(static descriptor => descriptor.Lifecycle is RuleLifecycle.Active)
            .Select(static descriptor => descriptor.Id)
            .OrderBy(static id => id.Value, StringComparer.Ordinal);
        var accounted = completed.ExecutedRules
            .Concat(completed.SkippedRules)
            .OrderBy(static id => id.Value, StringComparer.Ordinal);
        Assert.Equal(active, accounted);
    }

    [Fact]
    public void AdvisoryIsSkippedWhenNoManagedLeanSourceChanged()
    {
        var completed = Execute(Pair(leftTouched: false, rightTouched: false));

        Assert.Contains(RuleId.CreateKnown(28), completed.SkippedRules);
        Assert.DoesNotContain(RuleId.CreateKnown(28), completed.ExecutedRules);
    }

    [Fact]
    public void DuplicateAcrossTwoTouchedModulesIsObservedOnce()
    {
        var diagnostic = Assert.Single(Evaluate(Pair(leftTouched: true, rightTouched: true)));

        Assert.Equal(RuleFixture.DuplicateLeftGid + ".lean", diagnostic.Path);
    }

    [Fact]
    public void DistinctStatementsInTouchedModulesAreSilent()
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.channel_monotone",
            RuleFixture.DuplicateStatementType);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.dpi_defect",
            RuleFixture.DistinctStatementType,
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Theory]
    [MemberData(nameof(GeneratedNames))]
    public void GeneratedNamesAreOutsideTheAdvisory(string declarationName)
    {
        Assert.Empty(Evaluate(CollidingCandidate(declarationName)));
    }

    [Theory]
    [MemberData(nameof(HumanNamesResemblingGeneratedOnes))]
    public void HumanNamesResemblingGeneratedOnesStillReportTheDuplicate(string declarationName)
    {
        var diagnostic = Assert.Single(Evaluate(CollidingCandidate(declarationName)));

        Assert.Contains(declarationName, diagnostic.Message, StringComparison.Ordinal);
    }

    // The census that motivated this rule found automatic instances to be the
    // largest source of colliding statements; the inspector records the Prop-valued
    // ones as theorems (caught by the inst marker clause), and this case pins the
    // def-recorded direction. Neither is proof work anybody duplicated.
    [Fact]
    public void AutomaticInstanceDefinitionsAreOutsideTheAdvisory()
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.instFixtureLeft",
            RuleFixture.DuplicateStatementType,
            kind: "def");
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.instFixtureRight",
            RuleFixture.DuplicateStatementType,
            kind: "def",
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    [Fact]
    public void TheoremExcludedFromStatementIdentityIsOutsideTheAdvisory()
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.channel_monotone",
            RuleFixture.DuplicateStatementType);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.dpi_defect",
            RuleFixture.DuplicateStatementType,
            includeInStatement: false,
            touched: true);

        Assert.Empty(Evaluate(fixture));
    }

    private static RuleFixture CollidingCandidate(
        string declarationName = "D5.S1.Phase.DuplicateRight.dpi_defect")
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.channel_monotone",
            RuleFixture.DuplicateStatementType);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            declarationName,
            RuleFixture.DuplicateStatementType,
            touched: true);
        return fixture;
    }

    private static RuleFixture Pair(bool leftTouched, bool rightTouched)
    {
        var fixture = new RuleFixture();
        fixture.AddStatementModule(
            RuleFixture.DuplicateLeftGid,
            "D5.S0.Carrier.DuplicateLeft.channel_monotone",
            RuleFixture.DuplicateStatementType,
            touched: leftTouched);
        fixture.AddStatementModule(
            RuleFixture.DuplicateRightGid,
            "D5.S1.Phase.DuplicateRight.dpi_defect",
            RuleFixture.DuplicateStatementType,
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
