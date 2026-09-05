namespace StrataLint.Scribe.Tests;

public sealed class MutualInformationDocumentTests
{
    [Fact]
    public void MutualInformationStatesNonnegativityAndItsHonestScope()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/MutualInformation");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Entropy/MutualInformation.mutual_information_nonneg",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\" +
            @"0\le \operatorname{mutualInformation}(p).\end{gathered}$$",
            latex);
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
