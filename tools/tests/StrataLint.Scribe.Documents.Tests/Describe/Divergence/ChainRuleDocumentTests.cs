namespace StrataLint.Scribe.Tests;

public sealed class ChainRuleDocumentTests
{
    [Fact]
    public void ChainRuleStatesTheFiniteRealIdentityAndItsHonestScope()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/ChainRule");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/ChainRule.kl_divergence_chain_rule",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var latex = LatexWriter.WriteStatement(
            describe.StatementFormula
                ?? throw new Xunit.Sdk.XunitException("Statement formula is required."));
        Assert.Contains(@"\sum_{j}p(i,j)", latex, StringComparison.Ordinal);
        Assert.Contains(@"\frac{p(i,j)}{p_{\iota}(i)}", latex, StringComparison.Ordinal);
        Assert.Contains(@"D(p\Vert\Vert q)=D(p_{\iota}\Vert\Vert q_{\iota})", latex, StringComparison.Ordinal);
        Assert.Contains(@"\sum_{i}p_{\iota}(i)D(p_{\kappa\mid i}\Vert\Vert q_{\kappa\mid i})", latex, StringComparison.Ordinal);
        Assert.DoesNotContain(@"\operatorname{Nonempty}", latex, StringComparison.Ordinal);
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
