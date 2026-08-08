using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DescribeLatexRuleTests
{
    [Fact]
    public void ProjectableHandAuthoredTheoremIsBlocked()
    {
        var capability = VerifiedScribeEmissions.Create(
            [],
            [],
            [
                new ScribeDescribeLatexRecord(
                    "D5/S3/Weil/LatexFixture#describe/critical-line",
                    "Blueprint/D5/S3/Weil/LatexFixture.scribe.cs",
                    Kind: "theorem",
                    HasValidLatex: true,
                    FormulaProvenance: "hand-authored",
                    ProjectionFailureReason: null),
            ]);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(23),
            new RuleFixture().Build(verifiedScribeEmissions: capability));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal("SL-023", diagnostic.RuleId.Value);
        Assert.Equal(DisplaySeverity.Error, diagnostic.DisplaySeverity);
        Assert.Equal(AdmissionEffect.Block, diagnostic.AdmissionEffect);
        Assert.Contains("must be Lean-derived", diagnostic.Message, StringComparison.Ordinal);
        Assert.Contains("critical-line", diagnostic.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ExpandEpochAcceptsValidLatexAndNonTheoremDescribeNodes()
    {
        var capability = VerifiedScribeEmissions.Create(
            [],
            [],
            [
                new ScribeDescribeLatexRecord(
                    "D5/S3/Weil/LatexFixture#describe/critical-line",
                    "Blueprint/D5/S3/Weil/LatexFixture.scribe.cs",
                    Kind: "theorem",
                    HasValidLatex: true,
                    FormulaProvenance: "lean-derived",
                    ProjectionFailureReason: null),
                new ScribeDescribeLatexRecord(
                    "D5/S3/Weil/LatexFixture#describe/context",
                    "Blueprint/D5/S3/Weil/LatexFixture.scribe.cs",
                    Kind: "remark",
                    HasValidLatex: false,
                    FormulaProvenance: "hand-authored",
                    ProjectionFailureReason: null),
            ]);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(23),
            new RuleFixture().Build(verifiedScribeEmissions: capability));

        Assert.Empty(evaluation.Diagnostics);
    }
}
