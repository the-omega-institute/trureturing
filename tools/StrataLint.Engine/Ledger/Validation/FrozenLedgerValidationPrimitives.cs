using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    private static FrozenFreezePayload ParseFreeze(
        JsonElement payload,
        FrozenMaterialCatalog catalog) =>
        ParseSnapshot(payload, catalog, "Freeze");

    private static FrozenFreezePayload ParseReanchor(
        JsonElement payload,
        FrozenMaterialCatalog catalog,
        out string previousEventHash)
    {
        var result = ParseSnapshot(payload, catalog, "Reanchor");
        previousEventHash = RequiredString(payload, "previous_event_hash");
        if (!FrozenHashSyntax.IsSha256(previousEventHash))
        {
            throw new FormatException("Reanchor previous_event_hash is malformed.");
        }

        return result;
    }

    private static FrozenFreezePayload ParseSnapshot(
        JsonElement payload,
        FrozenMaterialCatalog catalog,
        string eventType)
    {
        RequireEventPayloadFields(payload, eventType);
        var pathText = RequiredString(payload, "descriptor_selector");
        if (!RepoPath.TryCreate(pathText, out var path) || !catalog.ByPath.TryGetValue(path, out var expectedMaterial))
        {
            throw new FormatException($"{eventType} targets a non-Closed or unknown module {pathText}.");
        }

        var statementText = RequiredString(payload, "statement_id");
        if (!FrozenHashSyntax.IsSha256(statementText))
        {
            throw new FormatException($"{eventType} contains a malformed content address.");
        }

        var declarationStatementIds = ParseDeclarationStatementIds(payload);
        var prerequisites = RequiredStringArray(payload, "prerequisite_frozen_node_ids")
            .Select(item => FrozenHashSyntax.IsSha256(item)
                ? FrozenNodeId.Create(item)
                : throw new FormatException($"{eventType} prerequisite contains a malformed content address."))
            .ToImmutableArray();
        var result = new FrozenFreezePayload(
            pathText,
            declarationStatementIds,
            prerequisites,
            StatementId.Create(statementText));
        if (!result.DeclarationStatementIds.SequenceEqual(expectedMaterial.DeclarationStatementIds)
            || result.StatementId != expectedMaterial.StatementId
            || !result.PrerequisiteFrozenNodeIds.SequenceEqual(expectedMaterial.PrerequisiteFrozenNodeIds)
            || result.DescriptorSelector != expectedMaterial.RepoPath.Value)
        {
            throw new FormatException(
                $"{eventType} payload does not match recomputed material for {path.Value}.");
        }

        return result;
    }

    internal static void ValidateReanchorTransition(
        FrozenActiveEntry current,
        FrozenFreezePayload reanchor,
        string previousEventHash)
    {
        if (!string.Equals(current.EventHash, previousEventHash, StringComparison.Ordinal))
        {
            throw new FormatException(
                "Reanchor previous_event_hash does not name the current active event.");
        }

        if (current.Payload.CaseId != reanchor.CaseId
            || current.Payload.DescriptorSelector != reanchor.DescriptorSelector
            || current.Payload.StatementId != reanchor.StatementId
            || !current.Payload.DeclarationStatementIds.SequenceEqual(
                reanchor.DeclarationStatementIds))
        {
            throw new FormatException(
                "Reanchor may not change case, module, statement, or declaration identities.");
        }

        if (current.Payload.PrerequisiteFrozenNodeIds.SequenceEqual(
            reanchor.PrerequisiteFrozenNodeIds))
        {
            throw new FormatException("Reanchor must change prerequisite coordinates.");
        }
    }

    internal static ImmutableArray<FrozenDeclarationStatement> ParseDeclarationStatementIds(
        JsonElement payload) =>
        ParseDeclarationStatementArray(payload.GetProperty("declaration_statement_ids"));

    private static ImmutableArray<FrozenDeclarationStatement> ParseDeclarationStatementArray(
        JsonElement value)
    {
        if (value.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("declaration_statement_ids must be an array.");
        }

        var result = value.EnumerateArray().Select(item =>
        {
            RequireObjectFields(item, "declaration statement", "declaration_name_key", "kind", "statement_id");
            var statementId = RequiredString(item, "statement_id");
            if (!FrozenHashSyntax.IsSha256(statementId))
            {
                throw new FormatException("Declaration statement contains a malformed content address.");
            }

            return new FrozenDeclarationStatement(
                RequiredString(item, "declaration_name_key"),
                RequiredString(item, "kind"),
                StatementId.Create(statementId));
        }).ToImmutableArray();
        var sorted = result
            .OrderBy(static item => item.DeclarationNameKey, StringComparer.Ordinal)
            .ThenBy(static item => item.Kind, StringComparer.Ordinal)
            .ThenBy(static item => item.StatementId.Value, StringComparer.Ordinal);
        if (!result.SequenceEqual(sorted)
            || result.Select(static item => item.DeclarationNameKey).Distinct(StringComparer.Ordinal).Count()
                != result.Length)
        {
            throw new FormatException(
                "declaration_statement_ids must have unique names and canonical ordinal order.");
        }

        return result;
    }

    private static string ComputeCorpusRoot(
        string headHash,
        ImmutableArray<FrozenFreezePayload> activeFreezes)
    {
        var leaves = activeFreezes
            .Select(payload => (
                CaseId: FrozenLedgerCanonicalWriter.CaseId(
                    RepoPath.CreateKnown(payload.DescriptorSelector),
                    payload.StatementId),
                Hash: ComputeCaseLeaf(payload)))
            .OrderBy(static item => item.CaseId, StringComparer.Ordinal)
            .ThenBy(static item => item.Hash, StringComparer.Ordinal)
            .ToImmutableArray();
        var activeRoot = ComputeClassRoot("active-frozen", leaves.Select(static item => item.Hash).ToImmutableArray());
        var admitRoot = ComputeClassRoot("must-admit", ImmutableArray<string>.Empty);
        var rejectRoot = ComputeClassRoot("must-reject", ImmutableArray<string>.Empty);
        using var stream = new MemoryStream();
        stream.Write(FrozenContentHash.Raw(headHash).AsSpan());
        stream.Write(FrozenContentHash.Raw(activeRoot).AsSpan());
        stream.Write(FrozenContentHash.Raw(admitRoot).AsSpan());
        stream.Write(FrozenContentHash.Raw(rejectRoot).AsSpan());
        WriteUInt64(stream, (ulong)leaves.Length);
        WriteUInt64(stream, 0);
        WriteUInt64(stream, 0);
        Span<byte> version = stackalloc byte[sizeof(uint)];
        BinaryPrimitives.WriteUInt32BigEndian(version, 2);
        stream.Write(version);
        return FrozenContentHash.Compute(FrozenHashDomains.FrozenCorpus, stream.ToArray());
    }

    internal static string ComputeFrozenGraphRoot(
        IEnumerable<FrozenNodeMaterial> nodes)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            nodes = nodes
                .OrderBy(static node => node.FrozenNodeId.Value, StringComparer.Ordinal)
                .Select(static node => new
                {
                    frozen_node_id = node.FrozenNodeId.Value,
                    prerequisite_frozen_node_ids = node.PrerequisiteFrozenNodeIds
                        .OrderBy(static id => id.Value, StringComparer.Ordinal)
                        .Select(static id => id.Value),
                }),
            schema = "frozen-graph-v1",
        });
        return FrozenContentHash.Compute(
            FrozenHashDomains.FrozenGraph,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
    }

    internal static string ComputeCaseLeaf(FrozenFreezePayload payload)
    {
        var material = FrozenLedgerCanonicalWriter.FreezeElement(payload);
        return FrozenContentHash.Compute(
            FrozenHashDomains.FrozenCase,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
    }

    private static string ComputeClassRoot(string className, ImmutableArray<string> leaves)
    {
        using var stream = new MemoryStream();
        var name = System.Text.Encoding.UTF8.GetBytes(className);
        stream.Write(name);
        stream.WriteByte(0);
        WriteUInt64(stream, (ulong)leaves.Length);
        foreach (var leaf in leaves)
        {
            stream.Write(FrozenContentHash.Raw(leaf).AsSpan());
        }

        return FrozenContentHash.Compute(FrozenHashDomains.FrozenClass, stream.ToArray());
    }

    private static void WriteUInt64(Stream stream, ulong value)
    {
        Span<byte> bytes = stackalloc byte[sizeof(ulong)];
        BinaryPrimitives.WriteUInt64BigEndian(bytes, value);
        stream.Write(bytes);
    }

    private static bool HasExactObjectFields(JsonElement value, params string[] names)
    {
        if (value.ValueKind != JsonValueKind.Object)
        {
            return false;
        }

        var actual = value.EnumerateObject().Select(static property => property.Name).ToArray();
        return actual.Distinct(StringComparer.Ordinal).Count() == actual.Length
            && actual.Order(StringComparer.Ordinal)
                .SequenceEqual(names.Order(StringComparer.Ordinal), StringComparer.Ordinal);
    }

    private static void RequireObjectFields(JsonElement value, string label, params string[] names)
    {
        if (value.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"{label} must be an object.");
        }

        if (!HasExactObjectFields(value, names))
        {
            throw new FormatException($"{label} has unknown, missing, or duplicate fields.");
        }
    }

    private static string RequiredString(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property) && property.ValueKind == JsonValueKind.String
            ? property.GetString() ?? throw new FormatException($"{name} must not be null.")
            : throw new FormatException($"{name} must be a string.");

    private static int RequiredNonnegativeInteger(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property)
        && property.ValueKind == JsonValueKind.Number
        && property.TryGetInt32(out var result)
        && result >= 0
            ? result
            : throw new FormatException($"{name} must be a nonnegative integer.");

    private static ImmutableArray<string> RequiredStringArray(JsonElement value, string name)
    {
        if (!value.TryGetProperty(name, out var property) || property.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException($"{name} must be an array.");
        }

        var result = property.EnumerateArray()
            .Select(item => item.ValueKind == JsonValueKind.String
                ? item.GetString() ?? throw new FormatException($"{name} contains null.")
                : throw new FormatException($"{name} contains a non-string."))
            .ToImmutableArray();
        if (!result.SequenceEqual(result.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            throw new FormatException($"{name} must be distinct and ordinal-sorted.");
        }

        return result;
    }
}
