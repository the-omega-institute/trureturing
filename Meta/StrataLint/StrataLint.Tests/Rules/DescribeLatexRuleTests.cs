using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DescribeLatexRuleTests
{
    [Fact]
    public void ExpandEpochWarnsForTheoremClassDescribeWithoutLatex()
    {
        var capability = VerifiedScribeEmissions.Create(
            [],
            [],
            [
                new ScribeDescribeLatexRecord(
                    "D5/S3/Weil/LatexFixture#describe/critical-line",
                    "Blueprint/D5/S3/Weil/LatexFixture.scribe.cs",
                    RequiresLatex: true,
                    HasValidLatex: false),
            ]);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(23),
            new RuleFixture().Build(verifiedScribeEmissions: capability));

        var diagnostic = Assert.Single(evaluation.Diagnostics);
        Assert.Equal("SL-023", diagnostic.RuleId.Value);
        Assert.Equal(DisplaySeverity.Warning, diagnostic.DisplaySeverity);
        Assert.Equal(AdmissionEffect.Observe, diagnostic.AdmissionEffect);
        Assert.Contains("SCRIBE-LATEX-EPOCH", diagnostic.Message, StringComparison.Ordinal);
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
                    RequiresLatex: true,
                    HasValidLatex: true),
                new ScribeDescribeLatexRecord(
                    "D5/S3/Weil/LatexFixture#describe/context",
                    "Blueprint/D5/S3/Weil/LatexFixture.scribe.cs",
                    RequiresLatex: false,
                    HasValidLatex: false),
            ]);

        var evaluation = RuleCatalog.Default.EvaluateSingle(
            RuleId.CreateKnown(23),
            new RuleFixture().Build(verifiedScribeEmissions: capability));

        Assert.Empty(evaluation.Diagnostics);
    }
}
