namespace StrataLint.Scribe.Tests;

public sealed class EntropyDivergenceIdentityDocumentTests
{
    [Fact]
    public void EntropyDivergenceIdentityStatesTheConsistencyPinAndItsResidualBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/EntropyDivergenceIdentity");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Entropy/EntropyDivergenceIdentity.kl_divergence_uniform_eq",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

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

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "The theorem identifies the divergence of p from the uniform law with the entropy deficit log |iota| - H(p).",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Both sides use the repository's existing imported definitions, klDivergence and shannonEntropy; this module defines nothing of its own.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The units are nats, consistent with klDivergence and shannonEntropy.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This equality is a consistency pin between the two definitions.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "On the probability simplex, it fixes shannonEntropy pointwise, but only because klDivergence is independently attested by other frozen identities.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The anchor is klDivergence; this is a pin between the two definitions, not an isolated certificate of entropy.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The residual limitation is plain: the identity is blind to every correction that vanishes on normalized inputs.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "For example, adding a multiple of (sum_i p(i) - 1) to shannonEntropy is invisible under the theorem's hypotheses, because the corrupted entropy agrees with the true one everywhere those hypotheses hold.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Off-simplex behaviour therefore remains unpinned; the theorem does not fully machine-attest the entropy definition.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The reference is specifically the uniform law i -> (card iota)^-1.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The identity does not hold against a non-uniform reference.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "A definition named uniform is deliberately not frozen in this bucket: it has a single consumer, so the reference is written inline.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The hypotheses are nonnegativity and normalization only, not strict positivity.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Zero-mass letters are permitted, and their terms vanish.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The Nonempty iota hypothesis is genuinely required, not decorative: the proof needs positive cardinality.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The same relation is derived inside MaxEntropy's proof as a proof-local step, but that step is not citable from outside the proof.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "This theorem is the first citable source of the fact and introduces no new definition.",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Frozen modules cannot gain declarations, so the relation is re-proved here rather than lifted out of MaxEntropy.",
            prose,
            StringComparison.Ordinal);
    }
}
