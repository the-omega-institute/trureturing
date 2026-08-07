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
        Assert.Equal("D5/L/watrous2018theory", describe.Provenance.LiteratureReference?.Value);

        var paragraph = Assert.IsType<DocumentBlock.Paragraph>(Assert.Single(describe.Content.Items));
        var prose = Assert.IsType<Inline.Text>(Assert.Single(paragraph.Content.Items)).Run.Value;
        Assert.Contains(
            "only the invariant-state existence base",
            prose,
            StringComparison.Ordinal);
        Assert.Contains("Theorem 4.5", prose, StringComparison.Ordinal);
        Assert.Contains("complete positivity", prose, StringComparison.Ordinal);
        Assert.Contains("tangent factor", prose, StringComparison.Ordinal);
        Assert.Contains("interior faithful invariant state", prose, StringComparison.Ordinal);
        Assert.Contains("remain separate open obligations", prose, StringComparison.Ordinal);
    }

    [Fact]
    public void WatrousNotePinsTheVerifiedLocatorWithoutInventingATheoremNumber()
    {
        var root = FindRepositoryRoot();
        var note = Assert.Single(
            LibraryNoteCatalog.Load(root).Notes,
            static item => item.BibKey.Value == "watrous2018theory");
        var text = File.ReadAllText(Path.Combine(root, note.RelativePath));

        Assert.Equal("10.1017/9781316848142", note.Doi?.Value);
        Assert.Equal(2018, note.Year);
        Assert.Contains("Section 4.4", text, StringComparison.Ordinal);
        Assert.Contains(
            "No specific theorem number is attributed",
            text,
            StringComparison.Ordinal);
    }

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null && !File.Exists(Path.Combine(directory.FullName, "CLAUDE.md")))
        {
            directory = directory.Parent;
        }

        return directory?.FullName
            ?? throw new DirectoryNotFoundException("Repository root was not found.");
    }
}
