namespace StrataLint.Scribe.Tests;

public sealed class ChannelFixedStateDocumentTests
{
    private const string DocumentGid = "D5/S3/Quantum/ChannelFixedState";

    [Fact]
    public void StatementMatchesTheLeanContextAndDisclosesTheOpenBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
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
        Assert.Equal(DescribeProvenanceKind.LiteratureAttested, describe.Provenance.Kind);
        Assert.Equal(
            "D5/L/Quantum/watrous2018theory",
            describe.Provenance.LiteratureReference?.Value);

        var paragraph = Assert.IsType<DocumentBlock.Paragraph>(Assert.Single(describe.Content.Items));
        Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items));
    }

    [Fact]
    public void WatrousNotePinsTheVerifiedLocatorWithoutInventingATheoremNumber()
    {
        var repository = RepositoryAccessor.Discover();
        var note = Assert.Single(
            LibraryNoteCatalog.Load(repository.Root.FullPath).Notes,
            static item => item.BibKey.Value == "watrous2018theory");
        var text = repository.ReadAllText(RepositoryRelativePath.Create(note.RelativePath));

        Assert.Equal("10.1017/9781316848142", note.Doi?.Value);
        Assert.Equal(2018, note.Year);
        Assert.Contains("Section 4.4", text, StringComparison.Ordinal);
        Assert.Contains(
            "No specific theorem number is attributed",
            text,
            StringComparison.Ordinal);
    }
}
