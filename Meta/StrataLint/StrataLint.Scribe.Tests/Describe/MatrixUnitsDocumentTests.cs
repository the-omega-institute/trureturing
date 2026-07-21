namespace StrataLint.Scribe.Tests;

public sealed class MatrixUnitsDocumentTests
{
    [Fact]
    public void MatrixUnitsCarriesSixStrongTheoremsAndKeepsObserverBridgesResidual()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Quantum/MatrixUnits");
        var describes = definition.Document.Content.Items
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(6, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            Assert.Equal(DescribeProvenanceKind.LiteratureAttested, describe.Provenance.Kind);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
            Assert.True(lean.Value.RequireNoSorry);
        });
        Assert.Equal(
            [
                "D5/S3/Quantum/MatrixUnits.qudit_weyl_relation",
                "D5/S3/Quantum/MatrixUnits.qudit_phase_order",
                "D5/S3/Quantum/MatrixUnits.qudit_shift_order",
                "D5/S3/Quantum/MatrixUnits.matrix_unit_certificate_error_zero",
                "D5/S3/Quantum/MatrixUnits.matrix_units_generate_full_algebra",
                "D5/S3/Quantum/MatrixUnits.matrix_algebra_has_no_character",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));
        Assert.Equal(
            [
                "D5/L/schwinger1960unitary",
                "D5/L/schwinger1960unitary",
                "D5/L/schwinger1960unitary",
                "D5/L/schwinger1960unitary",
                "D5/L/schwinger1960unitary",
                "D5/L/murphy1990calgebras",
            ],
            describes.Select(static describe => describe.Provenance.LiteratureReference?.Value));

        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(
                definition.Document,
                report,
                RepositoryCitations()).AsSpan());
        Assert.Contains("does not identify an arbitrary observer window", markdown,
            StringComparison.Ordinal);
        Assert.Contains("prime-power tensor factorization remains residual", markdown,
            StringComparison.Ordinal);
        Assert.Contains("Robertson variance inequality remains residual", markdown,
            StringComparison.Ordinal);
    }

    private static IReadOnlyDictionary<string, LiteratureCitation> RepositoryCitations()
    {
        var root = FindRepositoryRoot();
        return LibraryNoteCatalog.Load(root).Citations;
    }

    private static string FindRepositoryRoot()
    {
        var current = new DirectoryInfo(AppContext.BaseDirectory);
        while (current is not null && !File.Exists(Path.Combine(current.FullName, "lakefile.toml")))
        {
            current = current.Parent;
        }

        return current?.FullName
            ?? throw new InvalidOperationException("repository root not found");
    }
}
