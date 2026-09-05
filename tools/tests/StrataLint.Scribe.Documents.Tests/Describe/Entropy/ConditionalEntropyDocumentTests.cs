namespace StrataLint.Scribe.Tests;

public sealed class ConditionalEntropyDocumentTests
{
    [Fact]
    public void ConditionalEntropyStatesTheDefinitionChainRuleAndHonestScope()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/ConditionalEntropy");
        var describes = definition.Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(2, describes.Length);
        Assert.Equal(
            "D5/S3/Entropy/ConditionalEntropy.conditionalEntropy",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[0].Statement).Value.Value);
        Assert.Equal(
            "D5/S3/Entropy/ConditionalEntropy.entropy_chain_rule",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describes[1].Statement).Value.Value);
        Assert.All(describes, static describe =>
        {
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });

        var conditionalEntropy = LatexWriter.WriteStatement(
            Assert.IsType<StatementSource.Authored>(describes[0].StatementSource).Presentation);
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"\operatorname{conditionalEntropy}(p):=" +
            @"\sum_{i}\operatorname{marginal}(p)(i)" +
            @"\operatorname{shannonEntropy}(\operatorname{conditional}(p,i))." +
            @"\end{gathered}$$",
            conditionalEntropy);

        var chainRule = LatexWriter.WriteStatement(
            describes[1].StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota, \kappa\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Fintype}(\kappa)],\\\forall p: \iota\times\kappa\to \mathbb{R},\\" +
            @"(\forall i, j, 0\le p(i,j)) \Rightarrow\\" +
            @"\operatorname{shannonEntropy}(p)=" +
            @"\operatorname{shannonEntropy}(\operatorname{marginal}(p))+" +
            @"\operatorname{conditionalEntropy}(p).\end{gathered}$$",
            chainRule);
        Assert.All(
            describes.SelectMany(static describe => describe.Content.Items)
                .OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
