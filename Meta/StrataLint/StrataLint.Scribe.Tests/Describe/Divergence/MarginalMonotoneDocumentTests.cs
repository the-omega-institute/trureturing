namespace StrataLint.Scribe.Tests;

public sealed class MarginalMonotoneDocumentTests
{
    [Fact]
    public void MarginalMonotonicityStatesTheCompositionAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/MarginalMonotone");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/MarginalMonotone.kl_divergence_marginal_le",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\operatorname{Fintype}(\iota)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{Fintype}(\kappa)", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<p(i,j)", latex, StringComparison.Ordinal);
        Assert.Contains(@"0<q(i,j)", latex, StringComparison.Ordinal);
        Assert.Contains(
            @"D(p_{\iota}\Vert\Vert q_{\iota}) \le D(p\Vert\Vert q)",
            latex,
            StringComparison.Ordinal);
        Assert.DoesNotContain(@"\operatorname{Nonempty}", latex, StringComparison.Ordinal);
        Assert.DoesNotContain("=1", latex, StringComparison.Ordinal);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "Only strict positivity of p and q is assumed",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "no normalization of either joint function is assumed",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/ChainRule.kl_divergence_chain_rule supplies the exact decomposition",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg supplies nonnegativity of each conditional divergence",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "Finset.sum_nonneg combines those pointwise bounds",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "normalization premises are discharged, not assumed",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "both conditionals sum to one, proved directly from the definitions",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "absolute-continuity premise is trivial here because both conditionals are strictly positive",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "The empty second coordinate is handled explicitly",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("no Nonempty hypothesis", prose, StringComparison.Ordinal);
        Assert.Contains(
            "finite real-valued klDivergence of ClassicalDPI",
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
            "monotonicity only under taking the first-coordinate marginal",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "does not claim a general data-processing inequality over arbitrary channels",
            prose,
            StringComparison.Ordinal);
    }
}
