namespace StrataLint.Scribe.Tests;

public sealed class EntropyDivergenceIdentityDocumentTests
{
    [Fact]
    public void EntropyDivergenceIdentityStatesTheConsistencyPinAndItsResidualBoundary()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/EntropyDivergenceIdentity");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Entropy/EntropyDivergenceIdentity.kl_divergence_uniform_eq",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Nonempty}(\iota)],\\\forall p: \iota\to \mathbb{R},\\" +
            @"((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\" +
            @"D(p\Vert\Vert (i\mapsto \operatorname{card}(\iota)^{-1}))=" +
            @"\log(\operatorname{card}(\iota))-H(p).\end{gathered}$$",
            latex);
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
