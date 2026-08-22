using System.Collections.Immutable;
using System.Text;
using System.Text.Json;

namespace Trureturing.Truth;

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
                prerequisite_frozen_node_ids = node.PrerequisiteFrozenNodeIds,
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

/// <summary>
/// Fail-closed reader for <c>truth-export.v1.json</c>. It enforces the exact field set, the schema /
/// version / dialect / producer identity, strict ascending order of nodes, axioms, prerequisite frozen
/// node ids, and declarations, and that every node carries at least one declaration. It ends by
/// re-serialising the parsed model and requiring the bytes to match the input exactly, so only canonical
/// bytes are accepted.
/// </summary>
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
            [
                "declarations",
                "frozen_node_id",
                "node_axiom_closure",
                "prerequisite_frozen_node_ids",
                "repo_path",
            ],
            "truth export node");
        var axioms = Array(element, "node_axiom_closure")
            .EnumerateArray()
            .Select(static item => item.ValueKind == JsonValueKind.String
                ? item.GetString() ?? throw new FormatException("Axiom closure entry is null.")
                : throw new FormatException("Axiom closure entry must be a string."))
            .ToImmutableArray();
        var prerequisites = Array(element, "prerequisite_frozen_node_ids")
            .EnumerateArray()
            .Select(static item => item.ValueKind == JsonValueKind.String
                ? item.GetString() ?? throw new FormatException("Prerequisite frozen node id entry is null.")
                : throw new FormatException("Prerequisite frozen node id entry must be a string."))
            .ToImmutableArray();
        var declarations = Array(element, "declarations")
            .EnumerateArray()
            .Select(ReadDeclaration)
            .ToImmutableArray();
        return new TruthExportNode(
            String(element, "repo_path"),
            String(element, "frozen_node_id"),
            axioms,
            declarations,
            prerequisites);
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
            RequireStrictOrder(node.PrerequisiteFrozenNodeIds, "prerequisite frozen node ids");
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
