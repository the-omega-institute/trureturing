namespace StrataLint.Scribe.Tests;

public sealed class ProductAdditivityDocumentTests
{
    [Fact]
    public void ProductAdditivityStatesTheFiniteRealIdentityAndItsMeasureBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/ProductAdditivity");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/ProductAdditivity.kl_divergence_product_additive",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\sum_{i}a(i)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{j}a'(j)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"\mapsto a(i)a'(j)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\mapsto b(i)b'(j)", latex, StringComparison.Ordinal);
        Assert.Contains(@"+D(a'\Vert\Vert b')", latex, StringComparison.Ordinal);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains("Only a and a' are normalized", prose, StringComparison.Ordinal);
        Assert.Contains(
            "The reference functions b and b' need only be strictly positive and are not assumed normalized",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "finite real-valued klDivergence of ClassicalDPI",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "evaluated genuinely on the product mass functions",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("not a measure-theoretic divergence", prose, StringComparison.Ordinal);
        Assert.Contains(
            "InformationTheory.klDiv_compProd_eq_add is not used",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "no bridge between the ENNReal measure divergence and this finite real sum is established here",
            prose,
            StringComparison.Ordinal);
    }
}
