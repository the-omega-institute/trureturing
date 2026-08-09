namespace StrataLint.Scribe.Tests;

public sealed class MaxEntropyDocumentTests
{
    [Fact]
    public void MaximumEntropyStatesTheFiniteBoundAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Entropy/MaxEntropy");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Entropy/MaxEntropy.entropy_le_log_card",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Equal(
            @"$$\begin{gathered}\forall \iota\ [\operatorname{Fintype}(\iota)] " +
            @"[\operatorname{Nonempty}(\iota)],\\\forall p: \iota\to \mathbb{R},\\" +
            @"((\forall i, 0\le p(i)) \land \sum_{i}p(i)=1) \Rightarrow\\" +
            @"\sum_{i}\operatorname{negMulLog}(p(i)) \le " +
            @"\log(\operatorname{card}(\iota)).\end{gathered}$$",
            latex);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "The units are nats: Real.log is the natural logarithm, consistent with the repository's klDivergence",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "deliberately wraps Mathlib's Real.negMulLog term by term and supplies only the finite sum that Mathlib does not provide",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Mathlib owns the per-term lemmas for nonnegativity on the unit interval, the product rule, and concavity",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "open-coding -sum p log p and re-deriving them would duplicate upstream work",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "introduces the uniform distribution u(i) = (card iota)^-1 locally",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "deliberately not frozen as a definition of this module because it has exactly one consumer",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg through the identity D(p||uniform) = log card - H(p)",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "no part of KL nonnegativity is re-proved here",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The hypotheses are nonnegativity and normalization only, not strict positivity",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("Zero-mass letters are permitted", prose, StringComparison.Ordinal);
        Assert.Contains(
            "Real.negMulLog 0 = 0 and Real.log 0 = 0",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "the same endpoint convention already fixed by klDivergence",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The Nonempty iota hypothesis is genuinely required, not decorative",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "without it the cardinality is zero and the uniform mass fails to be a distribution",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("This module proves the upper bound only", prose, StringComparison.Ordinal);
        Assert.Contains(
            "It does not characterize the equality case that the maximum is attained exactly at the uniform distribution",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "It introduces no conditional or joint entropy",
            prose,
            StringComparison.Ordinal);
    }
}
