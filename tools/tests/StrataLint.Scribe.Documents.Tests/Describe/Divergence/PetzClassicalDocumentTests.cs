namespace StrataLint.Scribe.Tests;

public sealed class PetzClassicalDocumentTests
{
    [Fact]
    public void PetzEqualityStatesTheSupportwisePosteriorCriterionAndItsBoundary()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/PetzClassical");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\Vert\Vert q", latex, StringComparison.Ordinal);
        Assert.Contains(@"\widehat{p}", latex, StringComparison.Ordinal);
        Assert.Contains(@"\Leftrightarrow", latex, StringComparison.Ordinal);
        Assert.Contains(@"\Rightarrow", latex, StringComparison.Ordinal);
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
