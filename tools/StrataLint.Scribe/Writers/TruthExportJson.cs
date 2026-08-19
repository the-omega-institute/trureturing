using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Scribe;

/// Canonical export of the base's STRICT-accepted active frozen truth.
///
/// The model PROJECTS the Engine's frozen material (FrozenNodeMaterial) to plain records whose
/// fields are all `.Value` strings; it never serialises FrozenNodeMaterial/StatementId/
/// FrozenNodeId/RepoPath/FrozenModuleAttestation directly, so the wire format stays independent of
/// Engine internals. `node_axiom_closure` is a NODE-level closure (the union over the node's
/// declarations), distinct from any single declaration's minimal closure; each declaration keeps
/// its own name-key, kind, and statement id. There is no truth_state field: every exported node is
/// invariantly Closed (it came from the strict active frozen set).
public sealed record TruthExportDeclaration(
    string DeclarationNameKey,
    string Kind,
    string StatementId);

public sealed record TruthExportNode(
    string RepoPath,
    string FrozenNodeId,
    ImmutableArray<string> NodeAxiomClosure,
    ImmutableArray<TruthExportDeclaration> Declarations);

public sealed record TruthExportModel(
    string Schema,
    int SchemaVersion,
    string Dialect,
    string SourceCommit,
    string SourceTree,
    string Producer,
    ImmutableArray<TruthExportNode> Nodes)
{
    /// Unversioned schema family.
    public const string SchemaName = "stratalint.truth-export";

    /// Versioned wire dialect; downstream consumers pin this as the only stable anchor.
    public const string CanonicalDialect = "stratalint.truth-export.v1";

    /// Stable producer identity. A version STRING, never an engine DLL/MVID hash. Bound to the CLI
    /// command name by a linkage test in StrataLint.Tests.
    public const string ProducerName = "TruthExportCommand";

    /// Git-ignored run-local residence, mirroring the truth-graph projection.
    public const string RelativePath = "Generated/truth-export.v1.json";

    public static TruthExportModel Create(
        ImmutableArray<FrozenNodeMaterial> activeNodes,
        string sourceCommit,
        string sourceTree)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(sourceCommit);
        ArgumentException.ThrowIfNullOrWhiteSpace(sourceTree);
        var nodes = activeNodes
            .Select(static node => new TruthExportNode(
                node.RepoPath.Value,
                node.FrozenNodeId.Value,
                node.AxiomClosure
                    .OrderBy(static axiom => axiom, StringComparer.Ordinal)
                    .ToImmutableArray(),
                node.DeclarationStatementIds
                    .Select(static declaration => new TruthExportDeclaration(
                        declaration.DeclarationNameKey,
                        declaration.Kind,
                        declaration.StatementId.Value))
                    .OrderBy(static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal)
                    .ThenBy(static declaration => declaration.StatementId, StringComparer.Ordinal)
                    .ToImmutableArray()))
            .OrderBy(static node => node.RepoPath, StringComparer.Ordinal)
            .ThenBy(static node => node.FrozenNodeId, StringComparer.Ordinal)
            .ToImmutableArray();
        return new TruthExportModel(
            SchemaName,
            1,
            CanonicalDialect,
            sourceCommit,
            sourceTree,
            ProducerName,
            nodes);
    }
}

public static class TruthExportJsonWriter
{
    public static ImmutableArray<byte> Write(TruthExportModel model)
    {
        ArgumentNullException.ThrowIfNull(model);
        var element = JsonSerializer.SerializeToElement(new
        {
            schema = model.Schema,
            schema_version = model.SchemaVersion,
            dialect = model.Dialect,
            source_commit = model.SourceCommit,
            source_tree = model.SourceTree,
            producer = model.Producer,
            nodes = model.Nodes.Select(static node => new
            {
                repo_path = node.RepoPath,
                frozen_node_id = node.FrozenNodeId,
                node_axiom_closure = node.NodeAxiomClosure,
                declarations = node.Declarations.Select(static declaration => new
                {
                    declaration_name_key = declaration.DeclarationNameKey,
                    kind = declaration.Kind,
                    statement_id = declaration.StatementId,
                }),
            }),
        });
        return StructuredCanonicalWriter.WriteJson(element);
    }
}

public static class TruthExportJsonReader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    public static TruthExportModel Read(ReadOnlySpan<byte> bytes)
    {
        try
        {
            var text = StrictUtf8.GetString(bytes);
            using var document = JsonDocument.Parse(text);
            var root = document.RootElement;
            RequireProperties(
                root,
                ["dialect", "nodes", "producer", "schema", "schema_version", "source_commit", "source_tree"],
                "truth export");
            var schema = String(root, "schema");
            var version = Integer(root, "schema_version");
            var dialect = String(root, "dialect");
            if (schema != TruthExportModel.SchemaName
                || version != 1
                || dialect != TruthExportModel.CanonicalDialect
                || dialect != $"{schema}.v{version}")
            {
                throw new FormatException("Truth export schema, version, or dialect is unsupported.");
            }

            var producer = String(root, "producer");
            if (producer != TruthExportModel.ProducerName)
            {
                throw new FormatException("Truth export producer identity is unsupported.");
            }

            var nodes = Array(root, "nodes").EnumerateArray().Select(ReadNode).ToImmutableArray();
            var model = new TruthExportModel(
                schema,
                version,
                dialect,
                String(root, "source_commit"),
                String(root, "source_tree"),
                producer,
                nodes);
            Validate(model);
            if (!TruthExportJsonWriter.Write(model).AsSpan().SequenceEqual(bytes))
            {
                throw new FormatException("Truth export JSON bytes are not canonical.");
            }

            return model;
        }
        catch (Exception exception) when (
            exception is JsonException or DecoderFallbackException or InvalidOperationException)
        {
            throw new FormatException("Truth export JSON is invalid.", exception);
        }
    }

    private static TruthExportNode ReadNode(JsonElement element)
    {
        RequireProperties(
            element,
            ["declarations", "frozen_node_id", "node_axiom_closure", "repo_path"],
            "truth export node");
        var axioms = Array(element, "node_axiom_closure")
            .EnumerateArray()
            .Select(static item => item.ValueKind == JsonValueKind.String
                ? item.GetString() ?? throw new FormatException("Axiom closure entry is null.")
                : throw new FormatException("Axiom closure entry must be a string."))
            .ToImmutableArray();
        var declarations = Array(element, "declarations")
            .EnumerateArray()
            .Select(ReadDeclaration)
            .ToImmutableArray();
        return new TruthExportNode(
            String(element, "repo_path"),
            String(element, "frozen_node_id"),
            axioms,
            declarations);
    }

    private static TruthExportDeclaration ReadDeclaration(JsonElement element)
    {
        RequireProperties(
            element,
            ["declaration_name_key", "kind", "statement_id"],
            "truth export declaration");
        return new TruthExportDeclaration(
            String(element, "declaration_name_key"),
            String(element, "kind"),
            String(element, "statement_id"));
    }

    private static void Validate(TruthExportModel model)
    {
        RequireStrictOrder(
            model.Nodes.Select(static node => node.RepoPath + "\0" + node.FrozenNodeId),
            "nodes");
        foreach (var node in model.Nodes)
        {
            RequireStrictOrder(node.NodeAxiomClosure, "node axiom closure");
            RequireStrictOrder(
                node.Declarations.Select(static declaration =>
                    declaration.DeclarationNameKey + "\0" + declaration.StatementId),
                "declarations");
            if (node.Declarations.IsEmpty)
            {
                throw new FormatException("Truth export node has no declarations.");
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
                throw new FormatException($"Truth export {name} must be sorted and unique.");
            }

            previous = value;
        }
    }

    private static JsonElement Array(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.Array
            ? value
            : throw new FormatException($"Truth export {name} must be an array.");

    private static string String(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
            ? value.GetString() ?? throw new FormatException($"Truth export {name} is null.")
            : throw new FormatException($"Truth export {name} must be a string.");

    private static int Integer(JsonElement parent, string name) =>
        parent.TryGetProperty(name, out var value) && value.TryGetInt32(out var result) && result >= 0
            ? result
            : throw new FormatException($"Truth export {name} must be a non-negative integer.");

    private static void RequireProperties(JsonElement element, IReadOnlyCollection<string> expected, string context)
    {
        if (element.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"Truth export {context} must be an object.");
        }

        var actual = element.EnumerateObject().Select(static property => property.Name).ToArray();
        if (actual.Length != expected.Count
            || !actual.Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal)))
        {
            throw new FormatException($"Truth export {context} has unexpected fields.");
        }
    }
}
