namespace StrataLint.Scribe.Tests;

public sealed class MutualInformationEntropyDocumentTests
{
    [Fact]
    public void MutualInformationEntropyStatesTheGeneralPinAndDerivedSubadditivity()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/MutualInformationEntropy");
        var describes = definition.Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(2, describes.Length);
        Assert.Equal(
            "D5/S3/Entropy/MutualInformationEntropy.mutual_information_eq_entropy_sub",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[0].Statement).Value.Value);
        Assert.Equal(
            "D5/S3/Entropy/MutualInformationEntropy.entropy_subadditive",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[1].Statement).Value.Value);
        Assert.All(describes, static describe =>
        {
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });

        var decomposition = LatexWriter.WriteStatement(
            describes[0].StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"(\forall i, j, 0\le p(i,j)) \Rightarrow\\" +
            @"\operatorname{mutualInformation}(p)=" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}(p))+" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}((j,i)\mapsto p(i,j)))-" +
            @"\operatorname{shannonEntropy}(p).\end{gathered}$$",
            decomposition);

        var subadditivity = LatexWriter.WriteStatement(
            describes[1].StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"((\forall i, j, 0\le p(i,j)) \land \sum_{i,j}p(i,j)=1) \Rightarrow\\" +
            @"\operatorname{shannonEntropy}(p)\le" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}(p))+" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}((j,i)\mapsto p(i,j)))." +
            @"\end{gathered}$$",
            subadditivity);
        Assert.All(
            describes.SelectMany(static describe => describe.Content.Items)
                .OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
