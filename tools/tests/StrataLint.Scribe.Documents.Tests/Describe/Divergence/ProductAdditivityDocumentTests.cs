namespace StrataLint.Scribe.Tests;

public sealed class ProductAdditivityDocumentTests
{
    [Fact]
    public void ProductAdditivityStatesTheFiniteRealIdentityAndItsMeasureBoundary()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/ProductAdditivity");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/ProductAdditivity.kl_divergence_product_additive",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\sum_{i}a(i)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{j}a'(j)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"\mapsto a(i)a'(j)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\mapsto b(i)b'(j)", latex, StringComparison.Ordinal);
        Assert.Contains(@"+D(a'\Vert\Vert b')", latex, StringComparison.Ordinal);
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
