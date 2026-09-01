using System.Text;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe.Tests;

public sealed class ReceiptStateNonInterferenceTests
{
    private const string SourceGid = "D5/S0/Test/ReceiptSource";
    private const string TargetGid = "D5/S0/Test/ReceiptTarget";

    [Fact]
    public void ReceiptStateDoesNotChangeDependencyEdgesOrCanonicalMarkdown()
    {
        var receiptFreeRoot = TemporaryRoot("receipt-free");
        var receiptBoundRoot = TemporaryRoot("receipt-bound");
        var definitions = Definitions();
        var report = LeanAxiomReport.Create(new Dictionary<string, LeanFileReport>
        {
            ["D5/S0/Test/ReceiptSource.lean"] = new(["D5.S0.Test.ReceiptTarget"], []),
            ["D5/S0/Test/ReceiptTarget.lean"] = new([], []),
        });

        try
        {
            WriteRepository(receiptFreeRoot, definitions, receiptBound: false);
            WriteRepository(receiptBoundRoot, definitions, receiptBound: true);

            var receiptFree = Capture(receiptFreeRoot, definitions, report);
            var receiptBound = Capture(receiptBoundRoot, definitions, report);

            Assert.Equal([TargetGid], receiptFree.Dependencies);
            Assert.Equal([TargetGid], receiptBound.Dependencies);
            Assert.Equal(receiptFree.Dependencies, receiptBound.Dependencies);
            Assert.Equal(receiptFree.Markdown, receiptBound.Markdown);
            Assert.True(receiptFree.Projection.Documents.DescribeNodes.SequenceEqual(
                receiptBound.Projection.Documents.DescribeNodes));
            Assert.True(receiptFree.Projection.Documents.DependencyEdges.SequenceEqual(
                receiptBound.Projection.Documents.DependencyEdges));
            Assert.True(receiptFree.Projection.Documents.NarrativeReferenceEdges.SequenceEqual(
                receiptBound.Projection.Documents.NarrativeReferenceEdges));
            Assert.True(receiptFree.Projection.Joins.TruthAnchors.SequenceEqual(
                receiptBound.Projection.Joins.TruthAnchors));
            Assert.True(receiptFree.Projection.Documents.Nodes
                .Select(static node => node with { Receipt = "receipt-state" })
                .SequenceEqual(receiptBound.Projection.Documents.Nodes
                    .Select(static node => node with { Receipt = "receipt-state" })));

            Assert.Equal("receipt-free", ReceiptFor(receiptFree.Projection, SourceGid));
            Assert.Equal("receipt-bound", ReceiptFor(receiptBound.Projection, SourceGid));
            Assert.Equal("receipt-free", ReceiptFor(receiptFree.Projection, TargetGid));
            Assert.Equal("receipt-free", ReceiptFor(receiptBound.Projection, TargetGid));
        }
        finally
        {
            TemporaryFileSystem.Directory.Delete(receiptFreeRoot, recursive: true);
            TemporaryFileSystem.Directory.Delete(receiptBoundRoot, recursive: true);
        }
    }

    private static Snapshot Capture(
        string repositoryRoot,
        IReadOnlyList<DocumentDefinition> definitions,
        LeanAxiomReport report)
    {
        var documents = definitions.Select(static definition => definition.Document).ToArray();
        var catalog = DeclarationCatalog.Create(report);
        var census = ReceiptFreeDocumentCatalog.Load(repositoryRoot, documents);
        var graph = DocumentGraphAssembler.Assemble(
            documents,
            catalog);
        Assert.Empty(graph.Findings);

        var projection = DocumentGraphExportProjection.Create(
            definitions.Select(definition => new DocumentGraphDocument(
                definition.RelativePath.Value,
                definition.Document,
                census.ReceiptFreeDocumentGids.Contains(definition.Document.Header.Gid.Value)
                    ? "receipt-free"
                    : "receipt-bound")),
            graph,
            catalog,
            new HashSet<string>(StringComparer.Ordinal));
        var output = new StringWriter();
        var error = new StringWriter();
        var exit = ScribeEmitter.Emit(
            repositoryRoot,
            check: false,
            output,
            error,
            report,
            definitions);
        Assert.True(exit == 0, $"emit exit={exit}: {error}");

        var source = definitions.Single(static definition =>
            definition.Document.Header.Gid.Value == SourceGid);
        return new Snapshot(
            graph.For(source.Document)
                .OfType<DocumentEdge.Dependency>()
                .Select(static edge => edge.Target.Value)
                .ToArray(),
            TemporaryFileSystem.File.ReadAllBytes(Path.Combine(
                repositoryRoot,
                source.RelativePath.Value)),
            projection);
    }

    private static IReadOnlyList<DocumentDefinition> Definitions() =>
    [
        Definition(SourceGid),
        Definition(TargetGid),
    ];

    private static DocumentDefinition Definition(string gid)
    {
        var document = ScribeDocument.Create(
            DefinitionDsl.Header(gid, "Receipt-state non-interference fixture."),
            DefinitionDsl.H(gid),
            DefinitionDsl.Blocks(
                DefinitionDsl.Paragraph(DefinitionDsl.Text("Fixture body."))));
        return DocumentDefinition.Create(document, $"Blueprint/{gid}.scribe.cs");
    }

    private static void WriteRepository(
        string repositoryRoot,
        IReadOnlyList<DocumentDefinition> definitions,
        bool receiptBound)
    {
        TemporaryFileSystem.Directory.CreateDirectory(repositoryRoot);
        foreach (var definition in definitions)
        {
            var sourcePath = Path.Combine(
                repositoryRoot,
                ScribeEmissionAttestation.DefinitionPath(definition.Document.Header.Gid.Value));
            TemporaryFileSystem.Directory.CreateDirectory(Path.GetDirectoryName(sourcePath)!);
            TemporaryFileSystem.File.WriteAllText(
                sourcePath,
                "// receipt-state non-interference fixture\n",
                new UTF8Encoding(false, true));
        }

        var ledgerRoot = Path.Combine(
            repositoryRoot,
            "Meta", "Digestion", "backfill", "synthetic-source");
        TemporaryFileSystem.Directory.CreateDirectory(ledgerRoot);
        TemporaryFileSystem.File.WriteAllText(
            Path.Combine(ledgerRoot, "source.toml"),
            """
            source_id = "synthetic-source"
            path = "docs/synthetic.md"
            atomizer = "synthetic-v1"
            genre_registry_check = "collected"
            unregistered_genres = []
            """ + "\n",
            new UTF8Encoding(false, true));
        if (!receiptBound)
        {
            return;
        }

        var absorbedClosed = Path.Combine(ledgerRoot, "absorbed-closed");
        TemporaryFileSystem.Directory.CreateDirectory(absorbedClosed);
        TemporaryFileSystem.File.WriteAllText(
            Path.Combine(
                absorbedClosed,
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
                - gid: {{SourceGid}}.formalized
                  definition_sha256: sha256:1111111111111111111111111111111111111111111111111111111111111111
                  emission_sha256: sha256:2222222222222222222222222222222222222222222222222222222222222222
              unresolved_subitems: []
              chain_atoms: []
              tail_authorization: null
            """ + "\n",
            new UTF8Encoding(false, true));
    }

    private static string ReceiptFor(DocumentGraphExportProjection projection, string gid) =>
        projection.Documents.Nodes.Single(node => string.Equals(
            node.Gid,
            gid,
            StringComparison.Ordinal)).Receipt;

    private static string TemporaryRoot(string state) => Path.Combine(
        Path.GetTempPath(),
        $"stratalint-scribe-{state}-{Guid.NewGuid():N}");

    private sealed record Snapshot(
        string[] Dependencies,
        byte[] Markdown,
        DocumentGraphExportProjection Projection);
}
