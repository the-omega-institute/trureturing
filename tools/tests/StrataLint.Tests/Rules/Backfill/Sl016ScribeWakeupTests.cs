using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class Sl016ScribeWakeupTests
{
    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void ResolverFindsReferencedScribeInputDependency(bool emissionOnly)
    {
        var (context, _) = Sl016WakeupTests.EvaluateReceiptIntegrityGap(
            mismatchCode: null,
            gapExistsInBaseline: false,
            candidateScribeInputsChanged: true,
            candidateScribeEmissionOnly: emissionOnly,
            includeRuleImplementationPath: false);
        var document = context.BackfillCandidateDeltaSession.GetDocument(context.Changes);

        Assert.True(BackfillDeltaImpactResolver.HasAffectedCoverageDependencies(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            document,
            context.Changes));
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RuleCatalogWakesSl016ForReferencedScribeInputOnly(bool emissionOnly)
    {
        var (context, _) = Sl016WakeupTests.EvaluateReceiptIntegrityGap(
            mismatchCode: null,
            gapExistsInBaseline: false,
            candidateScribeInputsChanged: true,
            candidateScribeEmissionOnly: emissionOnly,
            includeRuleImplementationPath: false);

        var outcome = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context));
        var finding = Assert.Single(outcome.Capability.Diagnostics, diagnostic =>
            diagnostic.RuleId == RuleId.CreateKnown(16)
            && diagnostic.Message.Contains(
                emissionOnly ? "scribe-emission-mismatch" : "scribe-definition-mismatch",
                StringComparison.Ordinal));
        Assert.Equal(AdmissionEffect.Block, finding.AdmissionEffect);
    }

    [Fact]
    public void RuleCatalogDoesNotWakeSl016ForUnrelatedScribeModule()
    {
        const string unrelatedPath = "Blueprint/D5/S0/Carrier/Unrelated.scribe.cs";
        var (context, _) = Sl016WakeupTests.EvaluateReceiptIntegrityGap(
            mismatchCode: null,
            gapExistsInBaseline: false,
            candidateScribeInputsChanged: true,
            includeRuleImplementationPath: false,
            unrelatedChangedPath: unrelatedPath);

        var outcome = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.Execute(context));

        Assert.DoesNotContain(outcome.Capability.ExecutedRules, id => id == RuleId.CreateKnown(16));
        Assert.Contains(outcome.Capability.SkippedRules, id => id == RuleId.CreateKnown(16));
    }
}
