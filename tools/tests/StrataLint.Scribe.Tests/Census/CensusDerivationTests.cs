using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class CensusDerivationTests
{
    [Fact]
    public void ReceiptClassificationRejectsAnEmptyDocumentCorpus()
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            ReceiptFreeDocumentCatalog.Load("not-read-for-empty-corpus", []));

        Assert.Contains("document corpus must not be empty", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void SyntheticDirectoryLedgerDeterminesCensusDirection()
    {
        const string receiptBoundGid = "D5/S0/Test/ReceiptBound";
        const string receiptFreeGid = "D5/S0/Test/ReceiptFree";
        var repositoryRoot = Path.Combine(
            Path.GetTempPath(),
            "stratalint-census-" + Guid.NewGuid().ToString("N"));
        var sourceRoot = Path.Combine(
            repositoryRoot,
            "Meta", "Digestion", "backfill", "synthetic-source");
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(sourceRoot, "absorbed-closed"));
        try
        {
            TemporaryFileSystem.File.WriteAllText(
                Path.Combine(sourceRoot, "source.toml"),
                """
                source_id = "synthetic-source"
                path = "docs/synthetic.md"
                atomizer = "synthetic-v1"
                genre_registry_check = "collected"
                unregistered_genres = []

                """.Replace("\r\n", "\n", StringComparison.Ordinal));
            TemporaryFileSystem.File.WriteAllText(
                Path.Combine(
                    sourceRoot,
                    "absorbed-closed",
                    "0000000000000000000000000000000000000000000000000000000000000000.yaml"),
                $$"""
                fingerprints:
                  raw_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                  normalized_sha256: sha256:0000000000000000000000000000000000000000000000000000000000000000
                cas_ref: sha256:0000000000000000000000000000000000000000000000000000000000000000
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe:
                    - gid: {{receiptBoundGid}}.formalized
                      definition_sha256: sha256:1111111111111111111111111111111111111111111111111111111111111111
                      emission_sha256: sha256:2222222222222222222222222222222222222222222222222222222222222222
                  unresolved_subitems: []
                  chain_atoms: []
                  tail_authorization: null
                """);
            var census = ReceiptFreeDocumentCatalog.Load(
                repositoryRoot,
                [Document(receiptBoundGid), Document(receiptFreeGid)]);

            Assert.Equal([receiptBoundGid], census.ReceiptBoundDocumentGids);
            Assert.Equal([receiptFreeGid], census.ReceiptFreeDocumentGids);
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(repositoryRoot, recursive: true);
        }
    }

    private static ScribeDocument Document(string gid) =>
        ScribeDocument.Create(
            DefinitionDsl.Header(gid, "Receipt census fixture."),
            DefinitionDsl.H(gid),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("fixture"))));
}
