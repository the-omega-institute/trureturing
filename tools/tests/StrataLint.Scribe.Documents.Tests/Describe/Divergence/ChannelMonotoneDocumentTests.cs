namespace StrataLint.Scribe.Tests;

public sealed class ChannelMonotoneDocumentTests
{
    [Fact]
    public void ChannelMonotonicityStatesTheRestatementAndItsHonestScope()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Divergence/ChannelMonotone");
        var describe = Assert.IsType<DocumentBlock.Describe>(
            Assert.Single(definition.Document.Content.Items));

        Assert.Equal(
            "D5/S3/Divergence/ChannelMonotone.kl_divergence_channel_le",
            Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value);
        DocumentFactAssertions.RepoDerived(describe);
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

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
        Assert.All(
            describe.Content.Items.OfType<DocumentBlock.Paragraph>(),
            static paragraph =>
                Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)));
    }
}
