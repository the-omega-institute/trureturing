namespace StrataLint.Scribe.Tests;

public sealed class PetzClassicalDocumentTests
{
    [Fact]
    public void PetzEqualityStatesTheSupportwisePosteriorCriterionAndItsBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/PetzClassical");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\Vert\Vert q", latex, StringComparison.Ordinal);
        Assert.Contains(@"\widehat{p}", latex, StringComparison.Ordinal);
        Assert.Contains(@"\Leftrightarrow", latex, StringComparison.Ordinal);
        Assert.Contains(@"\Rightarrow", latex, StringComparison.Ordinal);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains("on the support of Wp", prose, StringComparison.Ordinal);
        Assert.Contains("finite nonnegative-sum criterion", prose, StringComparison.Ordinal);
        Assert.Contains(
            "Bayesian reverse recovery and the permutation-channel specialization are not part of this declaration",
            prose,
            StringComparison.Ordinal);
    }
}
