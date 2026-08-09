namespace StrataLint.Scribe.Tests;

public sealed class ChannelMonotoneDocumentTests
{
    [Fact]
    public void ChannelMonotonicityStatesTheCompositionAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/ChannelMonotone");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\operatorname{Fintype}(X)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{Nonempty}(X)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{Fintype}(Y)", latex, StringComparison.Ordinal);
        Assert.DoesNotContain(@"\operatorname{Nonempty}(Y)", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<p(x)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{x}p(x)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<q(x)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{x}q(x)=1", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<W(x, y)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{y}W(x, y)=1", latex, StringComparison.Ordinal);
        Assert.Contains(
            @"D(Wp\Vert\Vert Wq) \le D(p\Vert\Vert q)",
            latex,
            StringComparison.Ordinal);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "strictly positive normalized real mass functions",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("strictly positive stochastic kernel", prose, StringComparison.Ordinal);
        Assert.Contains("every row sums to one", prose, StringComparison.Ordinal);
        Assert.Contains(
            "exactly the hypotheses required by the wave-3 identity; nothing beyond them is assumed",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "composition of repository results, not new divergence machinery",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/ClassicalDPI.classical_dpi_identity supplies the exact decomposition",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg supplies nonnegativity of each posterior divergence",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Finset.sum_nonneg combines those pointwise bounds",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("premises are discharged, not assumed", prose, StringComparison.Ordinal);
        Assert.Contains(
            "each posterior is strictly positive and sums to one, proved directly from the definitions",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "absolute-continuity premise is trivial because the second posterior is strictly positive",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "data-processing inequality that wave 11's D5/S3/Divergence/MarginalMonotone module explicitly did not claim",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "first-coordinate marginalization is the special case of forgetting a coordinate",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "finite real-valued klDivergence of ClassicalDPI",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "repository's single source for the definition",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("not a measure-theoretic divergence", prose, StringComparison.Ordinal);
        Assert.Contains(
            "InformationTheory.klDiv_compProd_eq_add is not used",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "no ENNReal/finite-sum bridge is established here",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "strict positivity of the kernel and of both input distributions is required",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Channels with zero transition probabilities and distributions with zero mass are outside this module's scope",
            prose,
            StringComparison.Ordinal);
    }
}
