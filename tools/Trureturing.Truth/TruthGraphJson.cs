using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace Trureturing.Truth;

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
