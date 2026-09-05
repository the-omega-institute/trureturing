namespace StrataLint.Scribe.Tests;

public sealed class MarginalMonotoneDocumentTests
{
    [Fact]
    public void MarginalMonotonicityStatesTheCompositionAndItsHonestScope()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/MarginalMonotone");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/MarginalMonotone.kl_divergence_marginal_le",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

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
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
