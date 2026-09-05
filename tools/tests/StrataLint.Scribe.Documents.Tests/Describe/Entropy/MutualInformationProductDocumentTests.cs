namespace StrataLint.Scribe.Tests;

public sealed class MutualInformationProductDocumentTests
{
    [Fact]
    public void MutualInformationProductStatesTheIndependencePinAndItsResidualBoundary()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/MutualInformationProduct");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Entropy/MutualInformationProduct.mutual_information_product_eq_zero",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall a: \iota\to \mathbb{R}, " +
            @"b: \kappa\to \mathbb{R},\\" +
            @"((\forall i, 0\le a(i)) \land \sum_{i}a(i)=1) \land\\" +
            @"((\forall j, 0\le b(j)) \land \sum_{j}b(j)=1) \Rightarrow\\" +
            @"\operatorname{mutualInformation}((i,j)\mapsto a(i)b(j))=0.\end{gathered}$$",
            latex);
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
