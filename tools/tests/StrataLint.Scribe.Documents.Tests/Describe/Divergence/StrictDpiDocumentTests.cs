namespace StrataLint.Scribe.Tests;

public sealed class StrictDpiDocumentTests
{
    [Fact]
    public void StrictDpiStatesTheCompositionAndItsHonestScope()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/StrictDpi");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/StrictDpi.dpi_defect_pos_of_posteriors_ne",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.True(latex.Contains(@"\operatorname{Fintype}(X)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\operatorname{Nonempty}(X)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\operatorname{Fintype}(Y)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<p(x)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<q(x)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<W(x, y)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\exists y: Y", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\widehat{p}_{y}\neq\widehat{q}_{y}", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<D(p\Vert\Vert q)-D(Wp\Vert\Vert Wq)", StringComparison.Ordinal));
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
