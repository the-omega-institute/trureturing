using System.Collections.Immutable;
using System.Buffers.Binary;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

public sealed record TruthGraphProvenance(
    string SnapshotContentDigest,
    string LeanReportDigest)
{
    public string TruthRootSha256 { get; init; } = string.Empty;

    public string DependencyGranularity { get; init; } = "module-import";
}

public static class TruthGraphSnapshotIdentity
{
    private static readonly byte[] ProjectionMarker = Encoding.UTF8.GetBytes("scribe-generated-projection-v1");
    private static readonly ImmutableHashSet<string> GeneratedPaths = GeneratedArtifactInventory.All
        .Select(static artifact => artifact.Path)
        .ToImmutableHashSet(StringComparer.Ordinal);

    public static string Compute(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        Append(hash, "repository-snapshot-v1");
        foreach (var file in snapshot.Files.Values.OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
        {
            Append(hash, file.Path.Value);
            var contentHash = GeneratedPaths.Contains(file.Path.Value)
                ? SHA256.HashData(ProjectionMarker)
                : SHA256.HashData(file.RawBytes.AsSpan());
            Append(hash, contentHash);
        }

        return "sha256:" + Convert.ToHexStringLower(hash.GetHashAndReset());
    }

    private static void Append(IncrementalHash hash, string value) => Append(hash, Encoding.UTF8.GetBytes(value));

    private static void Append(IncrementalHash hash, ReadOnlySpan<byte> value)
    {
        Span<byte> length = stackalloc byte[sizeof(int)];
        BinaryPrimitives.WriteInt32LittleEndian(length, value.Length);
        hash.AppendData(length);
        hash.AppendData(value);
    }
}

public sealed record TruthGraphNode(
    string RepoPath,
    string? Gid,
    string State,
    string? ModuleName,
    int Depth);

public sealed record TruthGraphEdge(string Dependency, string Dependent);

public sealed record TruthGraphOpenBlocker(string Dependent, string DependencyModule);

public sealed record TruthGraphStateCounts(int Closed, int Open, int Tail, int Semantic)
{
    public int Total => Closed + Open + Tail + Semantic;
}

public sealed record TruthGraphSection(
    ImmutableArray<TruthGraphNode> Nodes,
    ImmutableArray<TruthGraphEdge> Edges,
    ImmutableArray<TruthGraphOpenBlocker> OpenBlockers,
    TruthGraphStateCounts StateCounts);

public sealed record DocumentGraphDocument(
    string RepoPath,
    ScribeDocument Document,
    string Receipt);

public sealed record DocumentGraphNode(string RepoPath, string Gid, string Receipt);

public sealed record DocumentDependencyEdge(string Dependency, string Dependent);

public sealed record DocumentNarrativeReferenceEdge(string Source, string Target);

public sealed record DescribeGraphNode(
    string RepoPath,
    string DocumentGid,
    string DescribeId,
    string Kind,
    string? LeanDeclarationGid,
    string FormulaProvenance);

public sealed record DocumentGraphSection(
    ImmutableArray<DocumentGraphNode> Nodes,
    ImmutableArray<DescribeGraphNode> DescribeNodes,
    ImmutableArray<DocumentDependencyEdge> DependencyEdges,
    ImmutableArray<DocumentNarrativeReferenceEdge> NarrativeReferenceEdges);

public sealed record TruthAnchorJoin(
    string DocumentRepoPath,
    string DocumentGid,
    string? DescribeId,
    string LeanDeclarationGid,
    string FormalTruthRepoPath);

public sealed record TruthGraphJoinsSection(ImmutableArray<TruthAnchorJoin> TruthAnchors);

public sealed record DocumentGraphExportProjection(
    DocumentGraphSection Documents,
    TruthGraphJoinsSection Joins)
{
    public static DocumentGraphExportProjection Empty { get; } = new(
        new DocumentGraphSection([], [], [], []),
        new TruthGraphJoinsSection([]));

    public static DocumentGraphExportProjection Create(
        IEnumerable<DocumentGraphDocument> documents,
        DocumentGraph graph,
        LeanAxiomReport leanReport,
        IReadOnlySet<string> formalTruthRepoPaths)
    {
        ArgumentNullException.ThrowIfNull(documents);
        ArgumentNullException.ThrowIfNull(graph);
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(formalTruthRepoPaths);
        if (!graph.Findings.IsEmpty)
        {
            throw new InvalidOperationException(
                $"Document graph is invalid: {graph.Findings[0].Code} {graph.Findings[0].Message}");
        }

        var catalog = DeclarationCatalog.Create(leanReport);
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
                        _ = LeanReferenceResolver.Resolve(anchor.Target, leanReport);
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

    public static DocumentGraphExportProjection AssembleRepository(
        string repositoryRoot,
        LeanAxiomReport leanReport,
        IReadOnlySet<string> formalTruthRepoPaths)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(formalTruthRepoPaths);
        var definitions = DocumentDefinitions.Discover(typeof(DocumentDefinitions).Assembly, repositoryRoot);
        var documents = definitions.Select(static definition => definition.Document).ToArray();
        var census = ReceiptFreeDocumentCatalog.Load(repositoryRoot, documents);
        var graph = DocumentGraphAssembler.Assemble(
            documents,
            leanReport,
            census.ReceiptFreeDocumentGids);
        var sources = definitions.Select(definition => new DocumentGraphDocument(
            definition.RelativePath.Value,
            definition.Document,
            census.ReceiptFreeDocumentGids.Contains(definition.Document.Header.Gid.Value)
                ? "receipt-free"
                : "receipt-bound"));
        return Create(sources, graph, leanReport, formalTruthRepoPaths);
    }
}

public sealed record TruthGraphExportModel(
    string Schema,
    int SchemaVersion,
    TruthGraphProvenance Provenance,
    TruthGraphSection Truth,
    DocumentGraphSection Documents,
    TruthGraphJoinsSection Joins,
    ImmutableArray<string> DeferredLayers)
{
    public const string Dialect = "stratalint.truth-graph.v1";

    public static TruthGraphExportModel Create(
        AcyclicTruthDag dag,
        TruthGraphProvenance provenance,
        DocumentGraphExportProjection? documentProjection = null)
    {
        ArgumentNullException.ThrowIfNull(dag);
        ArgumentNullException.ThrowIfNull(provenance);
        var nodes = dag.Nodes
            .OrderBy(static node => node.RepoPath.Value, StringComparer.Ordinal)
            .Select(node => new TruthGraphNode(
                node.RepoPath.Value,
                node.Gid?.Value,
                StateName(node.State),
                node.ModuleName,
                dag.Depth(node.RepoPath)))
            .ToImmutableArray();
        var edges = dag.Edges
            .OrderBy(static edge => edge.Dependency.Value, StringComparer.Ordinal)
            .ThenBy(static edge => edge.Dependent.Value, StringComparer.Ordinal)
            .Select(static edge => new TruthGraphEdge(edge.Dependency.Value, edge.Dependent.Value))
            .ToImmutableArray();
        var blockers = dag.OpenBlockers
            .OrderBy(static blocker => blocker.Dependent.Value, StringComparer.Ordinal)
            .ThenBy(static blocker => blocker.DependencyModule, StringComparer.Ordinal)
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
            Dialect,
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

public static class TruthGraphJsonWriter
{
    public static ImmutableArray<byte> Write(TruthGraphExportModel model)
    {
        ArgumentNullException.ThrowIfNull(model);
        var element = JsonSerializer.SerializeToElement(new
        {
            schema = model.Schema,
            schema_version = model.SchemaVersion,
            provenance = new
            {
                snapshot = new
                {
                    content_digest = model.Provenance.SnapshotContentDigest,
                    materializer = "repository-snapshot-v1",
                },
                lean_report_digest = model.Provenance.LeanReportDigest,
                truth_root_sha256 = model.Provenance.TruthRootSha256,
                dependency_granularity = model.Provenance.DependencyGranularity,
            },
            truth = new
            {
                nodes = model.Truth.Nodes.Select(static node => new
                {
                    repo_path = node.RepoPath,
                    gid = node.Gid,
                    state = node.State,
                    module_name = node.ModuleName,
                    depth = node.Depth,
                }),
                edges = model.Truth.Edges.Select(static edge => new
                {
                    dependency = edge.Dependency,
                    dependent = edge.Dependent,
                }),
                open_blockers = model.Truth.OpenBlockers.Select(static blocker => new
                {
                    dependent = blocker.Dependent,
                    dependency_module = blocker.DependencyModule,
                }),
                state_counts = new
                {
                    closed = model.Truth.StateCounts.Closed,
                    open = model.Truth.StateCounts.Open,
                    tail = model.Truth.StateCounts.Tail,
                    semantic = model.Truth.StateCounts.Semantic,
                },
            },
            documents = new
            {
                document_nodes = model.Documents.Nodes.Select(static node => new
                {
                    repo_path = node.RepoPath,
                    gid = node.Gid,
                    receipt = node.Receipt,
                }),
                describe_nodes = model.Documents.DescribeNodes.Select(static node => new
                {
                    repo_path = node.RepoPath,
                    document_gid = node.DocumentGid,
                    describe_id = node.DescribeId,
                    kind = node.Kind,
                    lean_declaration_gid = node.LeanDeclarationGid,
                    formula_provenance = node.FormulaProvenance,
                }),
                document_edges = new
                {
                    dependency = model.Documents.DependencyEdges.Select(static edge => new
                    {
                        dependency = edge.Dependency,
                        dependent = edge.Dependent,
                    }),
                    narrative_reference = model.Documents.NarrativeReferenceEdges.Select(static edge => new
                    {
                        source = edge.Source,
                        target = edge.Target,
                    }),
                },
            },
            joins = new
            {
                truth_anchors = model.Joins.TruthAnchors.Select(static anchor => new
                {
                    document_repo_path = anchor.DocumentRepoPath,
                    document_gid = anchor.DocumentGid,
                    describe_id = anchor.DescribeId,
                    lean_declaration_gid = anchor.LeanDeclarationGid,
                    formal_truth_repo_path = anchor.FormalTruthRepoPath,
                }),
            },
            deferred_layers = model.DeferredLayers,
        });
        return StructuredCanonicalWriter.WriteJson(element);
    }
}

public static class TruthGraphJsonReader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static TruthGraphExportModel Read(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var text = StrictUtf8.GetString(bytes);
            using var document = JsonDocument.Parse(text);
            var root = document.RootElement;
            RequireProperties(
                root,
                ["deferred_layers", "documents", "joins", "provenance", "schema", "schema_version", "truth"],
                "truth graph");
            var schema = String(root, "schema");
            var version = Integer(root, "schema_version");
            if (schema != TruthGraphExportModel.Dialect || version != 1)
            {
                throw new FormatException("Truth graph schema or version is unsupported.");
            }

            var provenanceElement = Object(root, "provenance");
            RequireProperties(
                provenanceElement,
                ["dependency_granularity", "lean_report_digest", "snapshot", "truth_root_sha256"],
                "provenance");
            var snapshot = Object(provenanceElement, "snapshot");
            RequireProperties(snapshot, ["content_digest", "materializer"], "snapshot");
            if (String(snapshot, "materializer") != "repository-snapshot-v1")
            {
                throw new FormatException("Truth graph snapshot materializer is unsupported.");
            }
            var provenance = new TruthGraphProvenance(
                String(snapshot, "content_digest"),
                String(provenanceElement, "lean_report_digest"))
            {
                TruthRootSha256 = String(provenanceElement, "truth_root_sha256"),
                DependencyGranularity = String(provenanceElement, "dependency_granularity"),
            };
            if (provenance.DependencyGranularity != "module-import")
            {
                throw new FormatException("Truth graph dependency granularity is unsupported.");
            }

            var truth = Object(root, "truth");
            RequireProperties(truth, ["edges", "nodes", "open_blockers", "state_counts"], "truth");
            var nodes = Array(truth, "nodes").EnumerateArray().Select(ReadNode).ToImmutableArray();
            var edges = Array(truth, "edges").EnumerateArray().Select(ReadEdge).ToImmutableArray();
            var blockers = Array(truth, "open_blockers").EnumerateArray().Select(ReadBlocker).ToImmutableArray();
            var countsElement = Object(truth, "state_counts");
            RequireProperties(countsElement, ["closed", "open", "semantic", "tail"], "state_counts");
            var counts = new TruthGraphStateCounts(
                Integer(countsElement, "closed"),
                Integer(countsElement, "open"),
                Integer(countsElement, "tail"),
                Integer(countsElement, "semantic"));

            var documentsElement = Object(root, "documents");
            RequireProperties(documentsElement, ["describe_nodes", "document_edges", "document_nodes"], "documents");
            var documentNodes = Array(documentsElement, "document_nodes")
                .EnumerateArray().Select(ReadDocumentNode).ToImmutableArray();
            var describeNodes = Array(documentsElement, "describe_nodes")
                .EnumerateArray().Select(ReadDescribeNode).ToImmutableArray();
            var documentEdges = Object(documentsElement, "document_edges");
            RequireProperties(documentEdges, ["dependency", "narrative_reference"], "document_edges");
            var dependencyEdges = Array(documentEdges, "dependency")
                .EnumerateArray().Select(ReadDocumentDependencyEdge).ToImmutableArray();
            var narrativeEdges = Array(documentEdges, "narrative_reference")
                .EnumerateArray().Select(ReadDocumentNarrativeEdge).ToImmutableArray();

            var joinsElement = Object(root, "joins");
            RequireProperties(joinsElement, ["truth_anchors"], "joins");
            var anchors = Array(joinsElement, "truth_anchors")
                .EnumerateArray().Select(ReadTruthAnchor).ToImmutableArray();
            var deferredLayers = Array(root, "deferred_layers")
                .EnumerateArray().Select(element => element.ValueKind == JsonValueKind.String
                    ? element.GetString() ?? throw new FormatException("Deferred layer is null.")
                    : throw new FormatException("Deferred layer must be a string."))
                .ToImmutableArray();
            var model = new TruthGraphExportModel(
                schema,
                version,
                provenance,
                new TruthGraphSection(nodes, edges, blockers, counts),
                new DocumentGraphSection(documentNodes, describeNodes, dependencyEdges, narrativeEdges),
                new TruthGraphJoinsSection(anchors),
                deferredLayers);
            Validate(model);
            if (!TruthGraphJsonWriter.Write(model).AsSpan().SequenceEqual(bytes))
            {
                throw new FormatException("Truth graph JSON bytes are not canonical.");
            }

            return model;
        }
        catch (Exception exception) when (exception is JsonException or DecoderFallbackException or InvalidOperationException)
        {
            throw new FormatException("Truth graph JSON is invalid.", exception);
        }
    }

    private static TruthGraphNode ReadNode(JsonElement element)
    {
        RequireProperties(element, ["depth", "gid", "module_name", "repo_path", "state"], "truth node");
        return new TruthGraphNode(
            String(element, "repo_path"),
            NullableString(element, "gid"),
            String(element, "state"),
            NullableString(element, "module_name"),
            Integer(element, "depth"));
    }

    private static TruthGraphEdge ReadEdge(JsonElement element)
    {
        RequireProperties(element, ["dependency", "dependent"], "truth edge");
        return new TruthGraphEdge(String(element, "dependency"), String(element, "dependent"));
    }

    private static TruthGraphOpenBlocker ReadBlocker(JsonElement element)
    {
        RequireProperties(element, ["dependency_module", "dependent"], "truth blocker");
        return new TruthGraphOpenBlocker(String(element, "dependent"), String(element, "dependency_module"));
    }

    private static DocumentGraphNode ReadDocumentNode(JsonElement element)
    {
        RequireProperties(element, ["gid", "receipt", "repo_path"], "document node");
        return new DocumentGraphNode(
            String(element, "repo_path"), String(element, "gid"), String(element, "receipt"));
    }

    private static DocumentDependencyEdge ReadDocumentDependencyEdge(JsonElement element)
    {
        RequireProperties(element, ["dependency", "dependent"], "document dependency edge");
        return new DocumentDependencyEdge(String(element, "dependency"), String(element, "dependent"));
    }

    private static DescribeGraphNode ReadDescribeNode(JsonElement element)
    {
        RequireProperties(element, ["describe_id", "document_gid", "formula_provenance", "kind", "lean_declaration_gid", "repo_path"], "describe node");
        return new DescribeGraphNode(String(element, "repo_path"), String(element, "document_gid"),
            String(element, "describe_id"), String(element, "kind"), NullableString(element, "lean_declaration_gid"),
            String(element, "formula_provenance"));
    }

    private static DocumentNarrativeReferenceEdge ReadDocumentNarrativeEdge(JsonElement element)
    {
        RequireProperties(element, ["source", "target"], "document narrative reference edge");
        return new DocumentNarrativeReferenceEdge(String(element, "source"), String(element, "target"));
    }

    private static TruthAnchorJoin ReadTruthAnchor(JsonElement element)
    {
        RequireProperties(
            element,
            ["describe_id", "document_gid", "document_repo_path", "formal_truth_repo_path", "lean_declaration_gid"],
            "truth anchor join");
        return new TruthAnchorJoin(
            String(element, "document_repo_path"),
            String(element, "document_gid"),
            NullableString(element, "describe_id"),
            String(element, "lean_declaration_gid"),
            String(element, "formal_truth_repo_path"));
    }

    private static void Validate(TruthGraphExportModel model)
    {
        RequireStrictOrder(model.Truth.Nodes.Select(static node => node.RepoPath), "nodes");
        RequireStrictOrder(model.Truth.Edges.Select(static edge => edge.Dependency + "\0" + edge.Dependent), "edges");
        RequireStrictOrder(model.Truth.OpenBlockers.Select(static blocker => blocker.Dependent + "\0" + blocker.DependencyModule), "open blockers");
        RequireStrictOrder(model.Documents.Nodes.Select(static node => node.RepoPath), "document nodes");
        RequireStrictOrder(model.Documents.DescribeNodes.Select(static node => node.RepoPath + "\0" + node.DescribeId), "describe nodes");
        RequireStrictOrder(
            model.Documents.DependencyEdges.Select(static edge => edge.Dependency + "\0" + edge.Dependent),
            "document dependency edges");
        RequireStrictOrder(
            model.Documents.NarrativeReferenceEdges.Select(static edge => edge.Source + "\0" + edge.Target),
            "document narrative reference edges");
        RequireStrictOrder(
            model.Joins.TruthAnchors.Select(static anchor =>
                anchor.DocumentRepoPath + "\0" + anchor.DescribeId + "\0" + anchor.LeanDeclarationGid),
            "truth anchor joins");
        var paths = model.Truth.Nodes.Select(static node => node.RepoPath).ToHashSet(StringComparer.Ordinal);
        var documentPaths = model.Documents.Nodes.Select(static node => node.RepoPath).ToHashSet(StringComparer.Ordinal);
        var documentGids = model.Documents.Nodes.Select(static node => node.Gid).ToHashSet(StringComparer.Ordinal);
        var documentIdentities = model.Documents.Nodes.ToDictionary(
            static node => node.RepoPath,
            static node => node.Gid,
            StringComparer.Ordinal);
        var describeIdentities = model.Documents.DescribeNodes
            .GroupBy(static node => (node.RepoPath, node.DocumentGid, node.DescribeId))
            .ToDictionary(static group => group.Key, static group => group.ToArray());
        if (model.Truth.Nodes.Any(node => node.Depth < 0 || node.State is not ("closed" or "open" or "tail" or "semantic"))
            || model.Truth.Edges.Any(edge => !paths.Contains(edge.Dependency) || !paths.Contains(edge.Dependent))
            || model.Truth.OpenBlockers.Any(blocker => !paths.Contains(blocker.Dependent))
            || model.Truth.StateCounts.Total != model.Truth.Nodes.Length
            || model.Truth.StateCounts.Closed != model.Truth.Nodes.Count(static node => node.State == "closed")
            || model.Truth.StateCounts.Open != model.Truth.Nodes.Count(static node => node.State == "open")
            || model.Truth.StateCounts.Tail != model.Truth.Nodes.Count(static node => node.State == "tail")
            || model.Truth.StateCounts.Semantic != model.Truth.Nodes.Count(static node => node.State == "semantic")
            || model.Documents.Nodes.Any(node => node.Receipt is not ("receipt-free" or "receipt-bound"))
            || documentGids.Count != model.Documents.Nodes.Length
            || model.Documents.DescribeNodes.Any(node => !documentPaths.Contains(node.RepoPath)
                || !documentGids.Contains(node.DocumentGid)
                || !string.Equals(
                    documentIdentities.GetValueOrDefault(node.RepoPath),
                    node.DocumentGid,
                    StringComparison.Ordinal)
                || node.FormulaProvenance is not ("hand-authored" or "lean-derived"))
            || model.Documents.DependencyEdges.Any(edge =>
                !documentPaths.Contains(edge.Dependency) || !documentPaths.Contains(edge.Dependent))
            || model.Documents.NarrativeReferenceEdges.Any(edge =>
                !documentPaths.Contains(edge.Source) || !documentPaths.Contains(DocumentTargetPath(edge.Target)))
            || model.Joins.TruthAnchors.Any(anchor =>
                !documentPaths.Contains(anchor.DocumentRepoPath)
                || !documentGids.Contains(anchor.DocumentGid)
                || !string.Equals(
                    documentIdentities.GetValueOrDefault(anchor.DocumentRepoPath),
                    anchor.DocumentGid,
                    StringComparison.Ordinal)
                || (anchor.DescribeId is not null
                    && (!describeIdentities.TryGetValue(
                            (anchor.DocumentRepoPath, anchor.DocumentGid, anchor.DescribeId),
                            out var matchingDescribes)
                        || matchingDescribes.Length != 1
                        || !string.Equals(
                            matchingDescribes[0].LeanDeclarationGid,
                            anchor.LeanDeclarationGid,
                            StringComparison.Ordinal)))
                || !paths.Contains(anchor.FormalTruthRepoPath))
            || !model.DeferredLayers.SequenceEqual(["digestion"], StringComparer.Ordinal))
        {
            throw new FormatException("Truth graph facts are inconsistent.");
        }

        foreach (var node in model.Truth.Nodes)
        {
            var dependencies = model.Truth.Edges.Where(edge => edge.Dependent == node.RepoPath).ToArray();
            var expected = dependencies.Length == 0
                ? 0
                : 1 + dependencies.Max(edge => model.Truth.Nodes.Single(candidate => candidate.RepoPath == edge.Dependency).Depth);
            if (node.Depth != expected)
            {
                throw new FormatException("Truth graph node depth is inconsistent.");
            }
        }
    }

    private static string DocumentTargetPath(string target)
    {
        var fragment = target.IndexOf('#', StringComparison.Ordinal);
        return fragment < 0 ? target : target[..fragment];
    }

    private static void RequireStrictOrder(IEnumerable<string> values, string name)
    {
        string? previous = null;
        foreach (var value in values)
        {
            if (previous is not null && string.CompareOrdinal(previous, value) >= 0)
            {
                throw new FormatException($"Truth graph {name} must be sorted and unique.");
            }

            previous = value;
        }
    }

    private static JsonElement Object(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.Object
            ? value
            : throw new FormatException($"Truth graph {name} must be an object.");

    private static JsonElement Array(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.Array
            ? value
            : throw new FormatException($"Truth graph {name} must be an array.");

    private static string String(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
            ? value.GetString() ?? throw new FormatException($"Truth graph {name} is null.")
            : throw new FormatException($"Truth graph {name} must be a string.");

    private static string? NullableString(JsonElement parent, string name)
    {
        if (!parent.TryGetProperty(name, out var value))
        {
            throw new FormatException($"Truth graph {name} is missing.");
        }

        return value.ValueKind switch
        {
            JsonValueKind.Null => null,
            JsonValueKind.String => value.GetString(),
            _ => throw new FormatException($"Truth graph {name} must be a string or null."),
        };
    }

    private static int Integer(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.TryGetInt32(out var result) && result >= 0
            ? result
            : throw new FormatException($"Truth graph {name} must be a non-negative integer.");

    private static void RequireProperties(JsonElement element, IReadOnlyCollection<string> expected, string context)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"Truth graph {context} must be an object.");
        }

        var actual = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (actual.Length != expected.Count
            || !actual.Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal)))
        {
            throw new FormatException($"Truth graph {context} has unexpected fields.");
        }
    }
}
