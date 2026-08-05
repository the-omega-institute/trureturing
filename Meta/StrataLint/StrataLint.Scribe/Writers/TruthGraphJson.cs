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
    private static readonly byte[] SelfMarker = Encoding.UTF8.GetBytes("truth-graph-self-projection-v1");

    public static string Compute(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        Append(hash, "repository-snapshot-v1");
        foreach (var file in snapshot.Files.Values.OrderBy(static file => file.Path.Value, StringComparer.Ordinal))
        {
            Append(hash, file.Path.Value);
            var contentHash = file.Path.Value == DagEmitter.TruthGraphRelativePath
                ? SHA256.HashData(SelfMarker)
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

public sealed record TruthGraphExportModel(
    string Schema,
    int SchemaVersion,
    TruthGraphProvenance Provenance,
    TruthGraphSection Truth)
{
    public const string Dialect = "stratalint.truth-graph.v1";

    public static TruthGraphExportModel Create(AcyclicTruthDag dag, TruthGraphProvenance provenance)
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
        return new TruthGraphExportModel(
            Dialect,
            1,
            provenance with
            {
                TruthRootSha256 = dag.RootSha256,
                DependencyGranularity = "module-import",
            },
            new TruthGraphSection(nodes, edges, blockers, counts));
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
            RequireProperties(root, ["provenance", "schema", "schema_version", "truth"], "truth graph");
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
            var model = new TruthGraphExportModel(
                schema,
                version,
                provenance,
                new TruthGraphSection(nodes, edges, blockers, counts));
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

    private static void Validate(TruthGraphExportModel model)
    {
        RequireStrictOrder(model.Truth.Nodes.Select(static node => node.RepoPath), "nodes");
        RequireStrictOrder(model.Truth.Edges.Select(static edge => edge.Dependency + "\0" + edge.Dependent), "edges");
        RequireStrictOrder(model.Truth.OpenBlockers.Select(static blocker => blocker.Dependent + "\0" + blocker.DependencyModule), "open blockers");
        var paths = model.Truth.Nodes.Select(static node => node.RepoPath).ToHashSet(StringComparer.Ordinal);
        if (model.Truth.Nodes.Any(node => node.Depth < 0 || node.State is not ("closed" or "open" or "tail" or "semantic"))
            || model.Truth.Edges.Any(edge => !paths.Contains(edge.Dependency) || !paths.Contains(edge.Dependent))
            || model.Truth.OpenBlockers.Any(blocker => !paths.Contains(blocker.Dependent))
            || model.Truth.StateCounts.Total != model.Truth.Nodes.Length
            || model.Truth.StateCounts.Closed != model.Truth.Nodes.Count(static node => node.State == "closed")
            || model.Truth.StateCounts.Open != model.Truth.Nodes.Count(static node => node.State == "open")
            || model.Truth.StateCounts.Tail != model.Truth.Nodes.Count(static node => node.State == "tail")
            || model.Truth.StateCounts.Semantic != model.Truth.Nodes.Count(static node => node.State == "semantic"))
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
