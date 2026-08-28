using System.Collections.Immutable;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Scribe;

public sealed record DocumentGraphDocument(
    string RepoPath,
    ScribeDocument Document,
    string Receipt);

/// Builds the moved <see cref="TruthGraphExportModel"/> from the Scribe-owned truth projection.
/// The model record lives in Trureturing.Truth (zero StrataLint dependency); this construction
/// step reads TruthDagProjection and therefore stays in Scribe, which references Engine.
public static class TruthGraphModelBuilder
{
    public static TruthGraphExportModel Create(
        TruthDagProjection dag,
        TruthGraphProvenance provenance,
        DocumentGraphExportProjection? documentProjection = null)
    {
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(provenance);
        var nodes = dag.Nodes
            .Select(node => new TruthGraphNode(
                node.RepoPath.Value,
                node.Gid?.Value,
                StateName(node.State),
                node.ModuleName,
                dag.Depth(node.RepoPath)))
            .ToImmutableArray();
        var edges = dag.Edges
            .Select(static edge => new TruthGraphEdge(edge.Dependency.Value, edge.Dependent.Value))
            .ToImmutableArray();
        var blockers = dag.OpenBlockers
            .Select(static blocker => new TruthGraphOpenBlocker(
                blocker.Dependent.Value,
                blocker.DependencyModule))
            .ToImmutableArray();
        var counts = new TruthGraphStateCounts(
            nodes.Count(static node => node.State == "closed"),
            nodes.Count(static node => node.State == "open"),
            nodes.Count(static node => node.State == "tail"),
            nodes.Count(static node => node.State == "semantic"));
        var projection = documentProjection ?? DocumentGraphExportProjection.Empty;
        return new TruthGraphExportModel(
            TruthGraphExportModel.Dialect,
            1,
            provenance with
            {
                TruthRootSha256 = dag.RootSha256,
                DependencyGranularity = "module-import",
            },
            new TruthGraphSection(nodes, edges, blockers, counts),
            projection.Documents,
            projection.Joins,
            ["digestion"]);
    }

    private static string StateName(TruthState state) => state switch
    {
        TruthState.Closed => "closed",
        TruthState.Open => "open",
        TruthState.Tail => "tail",
        TruthState.Semantic => "semantic",
        _ => throw new InvalidOperationException($"Unknown truth state {state}."),
    };
}

/// Builds the moved <see cref="DocumentGraphExportProjection"/> from Scribe/Engine document graph
/// material. The projection record lives in Trureturing.Truth; this assembly step depends on the
/// document AST and declaration catalog and therefore stays in Scribe.
public static class DocumentGraphExportProjectionExtensions
{
    extension(DocumentGraphExportProjection)
    {
        public static DocumentGraphExportProjection Create(
            IEnumerable<DocumentGraphDocument> documents,
            DocumentGraph graph,
            DeclarationCatalog catalog,
            IReadOnlySet<string> formalTruthRepoPaths)
        {
            ArgumentNullException.ThrowIfNull(documents);
            ArgumentNullException.ThrowIfNull(graph);
            ArgumentNullException.ThrowIfNull(catalog);
            ArgumentNullException.ThrowIfNull(formalTruthRepoPaths);
            if (!graph.Findings.IsEmpty)
            {
                throw new InvalidOperationException(
                    $"Document graph is invalid: {graph.Findings[0].Code} {graph.Findings[0].Message}");
            }

            var material = documents
                .Select(item => item with { Document = item.Document.ResolveDeclarations(catalog) })
                .ToImmutableArray();
            var byGid = material.ToDictionary(
                static item => item.Document.Header.Gid.Value,
                StringComparer.Ordinal);
            if (material.Select(static item => item.RepoPath).Distinct(StringComparer.Ordinal).Count() != material.Length)
            {
                throw new InvalidOperationException("Document graph export contains duplicate repository paths.");
            }
            if (material.Any(static item => item.Receipt is not ("receipt-free" or "receipt-bound")))
            {
                throw new InvalidOperationException("Document graph export contains an unsupported receipt category.");
            }

            var nodes = material
                .OrderBy(static item => item.RepoPath, StringComparer.Ordinal)
                .Select(static item => new DocumentGraphNode(
                    item.RepoPath,
                    item.Document.Header.Gid.Value,
                    item.Receipt))
                .ToImmutableArray();
            var dependencies = ImmutableArray.CreateBuilder<DocumentDependencyEdge>();
            var narratives = ImmutableArray.CreateBuilder<DocumentNarrativeReferenceEdge>();
            var anchors = ImmutableArray.CreateBuilder<TruthAnchorJoin>();
            var describeNodes = material.SelectMany(source => EnumerateDescribes(source.Document.Content)
                    .Select(describe => new DescribeGraphNode(
                        source.RepoPath,
                        source.Document.Header.Gid.Value,
                        describe.Id.Value,
                        DescribeVocabulary.CanonicalName(describe.Kind),
                        describe.Statement is DescribeStatement.LeanDeclaration lean ? lean.Value.Value : null,
                        describe.FormulaProvenance == StatementFormulaProvenance.LeanDerived ? "lean-derived" : "hand-authored")))
                .OrderBy(static node => node.RepoPath, StringComparer.Ordinal)
                .ThenBy(static node => node.DescribeId, StringComparer.Ordinal)
                .ToImmutableArray();
            foreach (var source in material)
            {
                foreach (var edge in graph.For(source.Document))
                {
                    switch (edge)
                    {
                        case DocumentEdge.Dependency dependency:
                            dependencies.Add(new DocumentDependencyEdge(
                                byGid[dependency.Target.Value].RepoPath,
                                source.RepoPath));
                            break;
                        case DocumentEdge.NarrativeReference narrative:
                            var targetGid = narrative.Target switch
                            {
                                NarrativeTarget.Document target => target.DocumentGid.Value,
                                NarrativeTarget.Describe target => target.DocumentGid.Value,
                                _ => throw new InvalidOperationException("Unknown narrative target."),
                            };
                            var fragment = narrative.Target is NarrativeTarget.Describe describe
                                ? $"#describe/{describe.DescribeId.Value}"
                                : string.Empty;
                            narratives.Add(new DocumentNarrativeReferenceEdge(
                                source.RepoPath,
                                byGid[targetGid].RepoPath + fragment));
                            break;
                        case DocumentEdge.TruthAnchor anchor:
                            _ = catalog.Resolve(DeclarationHandle.Create(anchor.Target.Value));
                            var formalPath = anchor.Target.Reference.Path.Value;
                            if (!formalTruthRepoPaths.Contains(formalPath))
                            {
                                throw new InvalidOperationException(
                                    $"Truth anchor {anchor.Target.Value} has no formal truth node {formalPath}.");
                            }
                            anchors.Add(new TruthAnchorJoin(
                                source.RepoPath,
                                source.Document.Header.Gid.Value,
                                anchor.DescribeId?.Value,
                                anchor.Target.Value,
                                formalPath));
                            break;
                    }
                }
            }

            return new DocumentGraphExportProjection(
                new DocumentGraphSection(
                    nodes,
                    describeNodes,
                    dependencies.OrderBy(static edge => edge.Dependency, StringComparer.Ordinal)
                        .ThenBy(static edge => edge.Dependent, StringComparer.Ordinal).ToImmutableArray(),
                    narratives.OrderBy(static edge => edge.Source, StringComparer.Ordinal)
                        .ThenBy(static edge => edge.Target, StringComparer.Ordinal).ToImmutableArray()),
                new TruthGraphJoinsSection(
                    anchors.OrderBy(static anchor => anchor.DocumentRepoPath, StringComparer.Ordinal)
                        .ThenBy(static anchor => anchor.DescribeId, StringComparer.Ordinal)
                        .ThenBy(static anchor => anchor.LeanDeclarationGid, StringComparer.Ordinal)
                        .ToImmutableArray()));
        }
    }

    private static IEnumerable<DocumentBlock.Describe> EnumerateDescribes(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            if (block is DocumentBlock.Describe describe)
            {
                yield return describe;
                foreach (var nested in EnumerateDescribes(describe.Content)) yield return nested;
            }
            else if (block is DocumentBlock.Section section)
            {
                foreach (var nested in EnumerateDescribes(section.Content)) yield return nested;
            }
        }
    }

    extension(DocumentGraphExportProjection)
    {
        public static DocumentGraphExportProjection AssembleRepository(
            string repositoryRoot,
            DeclarationCatalog catalog,
            IReadOnlySet<string> formalTruthRepoPaths)
        {
            ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
            ArgumentNullException.ThrowIfNull(catalog);
            ArgumentNullException.ThrowIfNull(formalTruthRepoPaths);
            var definitions = DocumentDefinitions.Discover(typeof(DocumentDefinitions).Assembly, repositoryRoot);
            var documents = definitions.Select(definition => definition.Document.ResolveDeclarations(catalog)).ToArray();
            var census = ReceiptFreeDocumentCatalog.Load(repositoryRoot, documents);
            var graph = DocumentGraphAssembler.Assemble(
                documents,
                catalog);
            var sources = definitions.Select(definition => new DocumentGraphDocument(
                definition.RelativePath.Value,
                definition.Document,
                census.ReceiptFreeDocumentGids.Contains(definition.Document.Header.Gid.Value)
                    ? "receipt-free"
                    : "receipt-bound"));
            return DocumentGraphExportProjection.Create(sources, graph, catalog, formalTruthRepoPaths);
        }
    }
}
