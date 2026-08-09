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
    public void ProductionReceiptClassificationIsDisjointAndComplete()
    {
        var repositoryRoot = FindRepositoryRoot();
        var documents = DocumentDefinitions.Discover(typeof(DocumentDefinitions).Assembly)
            .Select(static definition => definition.Document)
            .ToArray();
        var documentGids = documents
            .Select(static document => document.Header.Gid.Value)
            .ToHashSet(StringComparer.Ordinal);
        var census = ReceiptFreeDocumentCatalog.Load(
            repositoryRoot,
            documents);
        var receiptBoundDocumentGids = BackfillInventoryLoader.LoadRoot(repositoryRoot)
            .RequireDigestionEntries()
            .SelectMany(static entry => entry.Receipts.Scribe)
            .Select(static receipt => ScribeEmissionAttestation.DocumentGid(receipt.Gid))
            .ToHashSet(StringComparer.Ordinal);
        var receiptFreeDocumentGids = documentGids
            .Except(receiptBoundDocumentGids, StringComparer.Ordinal)
            .ToHashSet(StringComparer.Ordinal);
        var classified = census.ReceiptFreeDocumentGids
            .Union(census.ReceiptBoundDocumentGids, StringComparer.Ordinal)
            .ToHashSet(StringComparer.Ordinal);

        Assert.NotEmpty(documentGids);
        Assert.NotEmpty(receiptBoundDocumentGids);
        Assert.NotEmpty(receiptFreeDocumentGids);
        Assert.Empty(receiptBoundDocumentGids.Except(
            census.ReceiptBoundDocumentGids,
            StringComparer.Ordinal));
        Assert.Empty(receiptFreeDocumentGids.Except(
            census.ReceiptFreeDocumentGids,
            StringComparer.Ordinal));
        Assert.Empty(census.ReceiptFreeDocumentGids.Intersect(
            census.ReceiptBoundDocumentGids,
            StringComparer.Ordinal));
        Assert.Equal(documentGids.Order(StringComparer.Ordinal), classified.Order(StringComparer.Ordinal));
        Assert.Equal(
            documents.Length,
            census.ReceiptFreeDocumentGids.Count + census.ReceiptBoundDocumentGids.Count);
    }

    [Fact]
    public void SyntheticBackfillReceiptDeterminesCensusDirection()
    {
        const string receiptBoundGid = "D5/S0/Test/ReceiptBound";
        const string receiptFreeGid = "D5/S0/Test/ReceiptFree";
        var repositoryRoot = Path.Combine(
            Path.GetTempPath(),
            "stratalint-census-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(Path.Combine(repositoryRoot, "Meta"));
        try
        {
            File.WriteAllText(
                Path.Combine(repositoryRoot, BackfillInventoryLoader.RelativePath),
                $$"""
                schema_version: 3
                ledger: theory-digestion-v1
                sources:
                  - source_id: synthetic-source
                    path: docs/synthetic.md
                    atomizer: synthetic-v1
                    entries:
                      - atom_id: synthetic-atom
                        ast_path: theorem/synthetic
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
                        status:
                          migration: absorbed
                          truth: closed
                ticket_index: []
                """);
            var census = ReceiptFreeDocumentCatalog.Load(
                repositoryRoot,
                [Document(receiptBoundGid), Document(receiptFreeGid)]);

            Assert.Equal([receiptBoundGid], census.ReceiptBoundDocumentGids);
            Assert.Equal([receiptFreeGid], census.ReceiptFreeDocumentGids);
        }
        finally
        {
            Directory.Delete(repositoryRoot, recursive: true);
        }
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
        Directory.CreateDirectory(Path.Combine(sourceRoot, "absorbed-closed"));
        try
        {
            File.WriteAllText(
                Path.Combine(sourceRoot, "source.toml"),
                """
                source_id = "synthetic-source"
                path = "docs/synthetic.md"
                atomizer = "synthetic-v1"
                """);
            File.WriteAllText(
                Path.Combine(sourceRoot, "absorbed-closed", "synthetic-atom.yaml"),
                $$"""
                ast_path: theorem/synthetic
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
            File.WriteAllText(
                Path.Combine(repositoryRoot, "Meta", "Digestion", "ticket-index.toml"),
                string.Empty);
            var census = ReceiptFreeDocumentCatalog.Load(
                repositoryRoot,
                [Document(receiptBoundGid), Document(receiptFreeGid)]);

            Assert.Equal([receiptBoundGid], census.ReceiptBoundDocumentGids);
            Assert.Equal([receiptFreeGid], census.ReceiptFreeDocumentGids);
        }
        finally
        {
            Directory.Delete(repositoryRoot, recursive: true);
        }
    }

    private static string FindRepositoryRoot()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, "global.json"))
                && Directory.Exists(Path.Combine(current.FullName, "Blueprint")))
            {
                return current.FullName;
            }
        }

        throw new DirectoryNotFoundException("Could not locate the repository root.");
    }

    private static ScribeDocument Document(string gid) =>
        ScribeDocument.Create(
            DefinitionDsl.Header(gid, "Receipt census fixture."),
            DefinitionDsl.H(gid),
            DefinitionDsl.Blocks(DefinitionDsl.Paragraph(DefinitionDsl.Text("fixture"))));
}
