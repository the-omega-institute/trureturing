namespace StrataLint.Scribe.Tests;

public sealed class StrictDpiDocumentTests
{
    [Fact]
    public void StrictDpiStatesTheCompositionAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/StrictDpi");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/StrictDpi.dpi_defect_pos_of_posteriors_ne",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.True(latex.Contains(@"\operatorname{Fintype}(X)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\operatorname{Nonempty}(X)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\operatorname{Fintype}(Y)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<p(x)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<q(x)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<W(x, y)", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\exists y: Y", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"\widehat{p}_{y}\neq\widehat{q}_{y}", StringComparison.Ordinal));
        Assert.True(latex.Contains(@"0<D(p\Vert\Vert q)-D(Wp\Vert\Vert Wq)", StringComparison.Ordinal));

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "Strict DPI assumes strict positivity of p and q and of the stochastic kernel W",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "deliberately different from StrictGibbs's nonnegative absolutely continuous convention",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "the binders must not be copied between the two modules",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "posterior W p y is a quotient by channelOutput W p y",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "the posterior is defined, and is positive, only when that denominator is positive",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "StrictGibbs never divides, so discrete absolute continuity alone is enough to keep every logarithm meaningful",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The premise is not p ≠ q: it is ∃ y, posterior W p y ≠ posterior W q y",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Distinct inputs are neither the hypothesis of this theorem nor claimed by it to be sufficient",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "this module says nothing about whether p ≠ q alone forces a strictly positive defect",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/DpiDefect.dpi_defect_nonneg with D5/S3/Divergence/PetzClassical.dpi_defect_zero_iff_posteriors_eq",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("nothing is re-proved", prose, StringComparison.Ordinal);
        Assert.Contains(
            "PetzClassical's output-positivity side condition is discharged from these hypotheses",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("it is not assumed", prose, StringComparison.Ordinal);
        Assert.Contains(
            "zero transition probabilities and zero-mass distributions remain outside this module",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "the defect is zero if and only if the posteriors are equal, hence the defect is strictly positive exactly when they differ",
            prose,
            StringComparison.Ordinal);
    }
}
