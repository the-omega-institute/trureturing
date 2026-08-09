namespace StrataLint.Scribe.Tests;

public sealed class StrictGibbsDocumentTests
{
    [Fact]
    public void StrictGibbsStatesTheCompositionAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/StrictGibbs");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/StrictGibbs.kl_divergence_pos_of_ne",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.True(latex.Contains(@"\operatorname{Fintype}(I)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0\le p(i)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0\le q(i)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"q(i)=0 \Rightarrow p(i)=0", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"p\neq q", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<D(p\Vert q)", StringComparison.Ordinal));

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "Strict Gibbs assumes nonnegativity, normalization, and discrete absolute continuity",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("it does not assume strict positivity", prose, StringComparison.Ordinal);
        Assert.Contains(
            "deliberately different from the channel-side convention used by StrictDpi",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "the binders must not be copied between the two modules",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "StrictGibbs never divides, so discrete absolute continuity alone is enough to keep every logarithm meaningful",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "StrictDpi forms posteriors by quotienting by channelOutput W p y and therefore needs that denominator to be positive",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg with D5/S3/Divergence/GibbsEquality.kl_divergence_eq_zero_iff",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("nothing is re-proved", prose, StringComparison.Ordinal);
        Assert.Contains(
            "GrandmotherTheorem's own document records only nonnegativity and adds no equality characterization",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "finite real-valued klDivergence of ClassicalDPI",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("not a measure-theoretic divergence", prose, StringComparison.Ordinal);
    }
}
