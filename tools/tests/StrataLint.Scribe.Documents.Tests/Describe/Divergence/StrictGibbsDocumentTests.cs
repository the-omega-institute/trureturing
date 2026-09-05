namespace StrataLint.Scribe.Tests;

public sealed class StrictGibbsDocumentTests
{
    [Fact]
    public void StrictGibbsStatesTheCompositionAndItsHonestScope()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/StrictGibbs");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/StrictGibbs.kl_divergence_pos_of_ne",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.True(latex.Contains(@"\operatorname{Fintype}(I)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0\le p(i)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0\le q(i)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"q(i)=0 \Rightarrow p(i)=0", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"p\neq q", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<D(p\Vert q)", StringComparison.Ordinal));
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
