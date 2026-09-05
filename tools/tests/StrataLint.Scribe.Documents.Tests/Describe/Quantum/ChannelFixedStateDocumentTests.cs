namespace StrataLint.Scribe.Tests;

public sealed class ChannelFixedStateDocumentTests
{
    private const string DocumentGid = "D5/S3/Quantum/ChannelFixedState";

    [Fact]
    public void StatementMatchesTheLeanContextAndDisclosesTheOpenBoundary()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == DocumentGid);
        var describe = Assert.Single(
            definition.Document.Content.Items.OfType<DocumentBlock.Describe>());
        var formula = LatexWriter.WriteStatement(describe.StatementFormula!);

        Assert.Contains(@"\operatorname{Fintype}(n)", formula, StringComparison.Ordinal);
        Assert.Contains(@"\operatorname{Nonempty}(n)", formula, StringComparison.Ordinal);
        Assert.Contains(
            @"\operatorname{LinearMap}_{\mathbb{C}}",
            formula,
            StringComparison.Ordinal);
        DocumentFactAssertions.LiteratureAttested(
            describe,
            "D5/L/Quantum/watrous2018theory");
        DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);

        var paragraph = Assert.IsType<DocumentBlock.Paragraph>(Assert.Single(describe.Content.Items));
        Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items));
    }

}
