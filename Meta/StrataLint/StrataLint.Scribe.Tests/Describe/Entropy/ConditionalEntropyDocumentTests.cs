namespace StrataLint.Scribe.Tests;

public sealed class ConditionalEntropyDocumentTests
{
    [Fact]
    public void ConditionalEntropyStatesTheDefinitionChainRuleAndHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
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
        Assert.All(
            describes,
            static describe =>
                Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind));

        var conditionalEntropy = LatexWriter.WriteStatement(
            describes[0].StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
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

        var prose = string.Join(
            " ",
            describes.SelectMany(static describe => describe.Content.Items)
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "The joint entropy splits into the marginal entropy plus the marginal-weighted average of the conditional slice entropies.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This is the entropy-side counterpart of the frozen divergence chain rule.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The definitions of marginal and conditional come from D5/S3/Divergence/ChainRule; conditionalEntropy is the only new definition here.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It is introduced because the chain rule and queued conditional results all consume it, not speculatively.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The hypotheses are deliberately minimal: nonnegativity alone.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Normalization is not required, even though a reader may expect a probability distribution.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "When a marginal is zero, the conditional slice is a quotient by zero.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "That case is handled rather than excluded: nonnegativity forces every cell of such a slice to vanish, so the slice contributes nothing and the outer weight annihilates its term.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("No positivity is assumed anywhere.", prose, StringComparison.Ordinal);
        Assert.Contains(
            "On the nonnegative domain, the chain rule pins conditionalEntropy as the difference between two independently attested entropies.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "A wrong weight, a wrong slice association, or a slipped index that changes the aggregate would break the equality.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This pin constrains the aggregate only: a corruption that leaves the aggregate unchanged on every nonnegative joint would not be caught.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The units are nats because shannonEntropy uses Real.log.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This module proves no conditioning bound: the statement that conditioning cannot increase entropy is not proved here.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It proves no conditional mutual information, no equality condition, and nothing beyond two coordinates.",
            prose,
            StringComparison.Ordinal);
    }
}
