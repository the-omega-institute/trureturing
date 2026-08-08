namespace StrataLint.Scribe.Tests;

public sealed class ChainRuleDocumentTests
{
    [Fact]
    public void ChainRuleStatesTheFiniteRealIdentityAndItsHonestScope()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/ChainRule");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/ChainRule.kl_divergence_chain_rule",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\sum_{j}p(i,j)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\frac{p(i,j)}{p_{\iota}(i)}", latex, StringComparison.Ordinal);
        Assert.Contains(@"D(p\Vert\Vert q)=D(p_{\iota}\Vert\Vert q_{\iota})", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{i}p_{\iota}(i)D(p_{\kappa\mid i}\Vert\Vert q_{\kappa\mid i})", latex, StringComparison.Ordinal);
        Assert.DoesNotContain(@"\operatorname{Nonempty}", latex, StringComparison.Ordinal);

        var prose = string.Join(
            " ",
            describe.Content.Items
                .OfType<DocumentBlock.Paragraph>()
                .Select(static paragraph =>
                    Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value));
        Assert.Contains(
            "Only strict positivity is assumed; neither p nor q is assumed normalized",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("marginal r i = sum_j r(i,j)", prose, StringComparison.Ordinal);
        Assert.Contains(
            "conditional r i j = r(i,j) / marginal r i",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("the conditional is the genuine quotient", prose, StringComparison.Ordinal);
        Assert.Contains(
            "sum_j conditional p i j = 1 is proved from these definitions and strict positivity, not assumed",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("The empty second coordinate is handled explicitly", prose, StringComparison.Ordinal);
        Assert.Contains("no Nonempty hypothesis", prose, StringComparison.Ordinal);
        Assert.Contains("claims no normalization for an empty family", prose, StringComparison.Ordinal);
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
            "no bridge between the ENNReal measure divergence and this finite real sum is established here",
            prose,
            StringComparison.Ordinal);
        Assert.Contains(
            "D5/S3/Divergence/ProductAdditivity is the special case in which the conditionals do not depend on the first coordinate",
            prose,
            StringComparison.Ordinal);
    }
}
