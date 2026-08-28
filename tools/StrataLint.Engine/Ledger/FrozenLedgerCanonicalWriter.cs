using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal sealed record FrozenLedgerDraft(string EventType, JsonElement Payload);

internal static class FrozenLedgerGenerator
{
    internal static ImmutableArray<FrozenLedgerDraft> MissingFreezes(
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog candidateCatalog)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidateCatalog);
        var activeByPath = baseline.ActiveEntries.Values.ToDictionary(
            static entry => entry.Material.RepoPath,
            static entry => entry);
        return MissingFreezeEvents(activeByPath, candidateCatalog);
    }

    private static ImmutableArray<FrozenLedgerDraft> MissingFreezeEvents(
        IReadOnlyDictionary<RepoPath, FrozenActiveEntry> activeByPath,
        FrozenMaterialCatalog candidateCatalog)
    {
        var recordedPathsByIdentity = activeByPath.Values.ToDictionary(
            static entry => entry.Material.FrozenNodeId,
            static entry => entry.Material.RepoPath);
        var currentPathsByIdentity = activeByPath.Values
            .Select(static entry => entry.Material)
            .Concat(candidateCatalog.ClosedNodes)
            .GroupBy(static material => material.FrozenNodeId)
            .ToDictionary(
                static group => group.Key,
                static group => group.Select(static material => material.RepoPath).Distinct().Single());
        foreach (var (path, activeEntry) in activeByPath)
        {
            if (!candidateCatalog.ByPath.TryGetValue(path, out var candidate))
            {
                continue;
            }

            if (FrozenLedgerHistoricalFreezeMatcher.HistoricalActiveFreezeMatches(
                activeEntry.Payload,
                candidate,
                out _))
            {
                continue;
            }

            if (activeEntry.Payload.StatementId != candidate.StatementId
                || !activeEntry.Payload.DeclarationStatementIds.SequenceEqual(
                    candidate.DeclarationStatementIds))
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} statement identity changed; append Revoke before rerunning ledger-append.");
            }

            throw new InvalidOperationException(
                $"Active module {path.Value} changed identity; append Revoke before rerunning ledger-append.");
        }

        var payloads = candidateCatalog.ClosedNodes
            .Where(node => !activeByPath.ContainsKey(node.RepoPath))
            .Select(FrozenLedgerCanonicalWriter.FreezePayload)
            .OrderBy(static payload => payload.DescriptorSelector, StringComparer.Ordinal)
            .Select(static payload => new FrozenLedgerDraft(
                "Freeze",
                FrozenLedgerCanonicalWriter.FreezeElement(payload)))
            .ToImmutableArray();
        return payloads;
    }

}

internal static class FrozenLedgerCanonicalWriter
{
    internal const int CurrentDagSchemaVersion = 5;

    private static readonly string[] DagEnvelopeFields =
    [
        "event_hash", "event_type", "payload", "schema_version",
    ];

    internal static string CaseId(RepoPath path, StatementId statement)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            descriptor_selector = path.Value,
            schema = "frozen-case-identity-v1",
            statement_id = statement.Value,
        });
        var hash = FrozenContentHash.Compute(
            FrozenHashDomains.FrozenCaseIdentity,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
        return "active-frozen/" + hash[7..];
    }

    internal static FrozenFreezePayload FreezePayload(FrozenNodeMaterial node) =>
        new(
            node.RepoPath.Value,
            node.DeclarationStatementIds,
            node.PrerequisiteFrozenNodeIds,
            node.StatementId);

    internal static JsonElement FreezeElement(FrozenFreezePayload payload)
    {
        var element = JsonSerializer.SerializeToElement(new
        {
            declaration_statement_ids = payload.DeclarationStatementIds.Select(static declaration => new
            {
                declaration_name_key = declaration.DeclarationNameKey,
                kind = declaration.Kind,
                statement_id = declaration.StatementId.Value,
            }),
            descriptor_selector = payload.DescriptorSelector,
            prerequisite_frozen_node_ids = payload.PrerequisiteFrozenNodeIds.Select(static id => id.Value),
            statement_id = payload.StatementId.Value,
        });
        return element;
    }

    internal static (ImmutableArray<byte> Bytes, string Hash) WriteDagEvent(
        string eventType,
        JsonElement payload,
        int? schemaVersion = null)
    {
        if (eventType != "Freeze")
        {
            throw new ArgumentOutOfRangeException(nameof(eventType), "Only Freeze events are stored in ledger v5.");
        }

        var version = schemaVersion ?? CurrentDagSchemaVersion;
        if (version != CurrentDagSchemaVersion)
        {
            throw new ArgumentOutOfRangeException(
                nameof(schemaVersion),
                $"Content-addressed {eventType} schema_version must be {CurrentDagSchemaVersion}.");
        }

        return WriteDagEnvelope(eventType, payload, version);
    }

    internal static bool ValidateDagEvent(
        JsonElement value,
        out string identity,
        out string eventHash,
        out string message) =>
        ReadDagEvent(value, validateRecordedHash: true, out identity, out eventHash, out message);

    private static bool ReadDagEvent(
        JsonElement value,
        bool validateRecordedHash,
        out string identity,
        out string eventHash,
        out string message)
    {
        identity = string.Empty;
        eventHash = string.Empty;
        message = string.Empty;
        if (value.ValueKind != JsonValueKind.Object
            || !HasExactFields(value, DagEnvelopeFields))
        {
            message = "content-addressed event envelope has unknown, missing, or duplicate fields.";
            return false;
        }

        var eventType = value.GetProperty("event_type");
        var payload = value.GetProperty("payload");
        var schemaVersion = value.GetProperty("schema_version");
        var claimedHash = value.GetProperty("event_hash");
        if (eventType.ValueKind != JsonValueKind.String
            || payload.ValueKind != JsonValueKind.Object
            || !schemaVersion.TryGetInt32(out var version)
            || claimedHash.ValueKind != JsonValueKind.String)
        {
            message = "content-addressed event envelope has invalid field types.";
            return false;
        }

        var type = eventType.GetString()!;
        if (type != "Freeze")
        {
            message = $"content-addressed event type {type} is not legal in ledger v5.";
            return false;
        }

        if (version != CurrentDagSchemaVersion)
        {
            message = $"content-addressed {type} schema_version must be {CurrentDagSchemaVersion}.";
            return false;
        }

        eventHash = claimedHash.GetString()!;
        if (validateRecordedHash
            && !string.Equals(
                WriteDagEvent(type, payload, version).Hash,
                eventHash,
                StringComparison.Ordinal))
        {
            message = "event_hash does not match canonical content.";
            return false;
        }

        identity = EventIdentity(eventHash);
        return true;
    }

    internal static string EventIdentity(string eventHash) => eventHash;

    private static (ImmutableArray<byte> Bytes, string Hash) WriteDagEnvelope(
        string eventType,
        JsonElement payload,
        int schemaVersion)
    {
        var withoutHash = DagEnvelope(eventType, payload, schemaVersion, null);
        var hash = FrozenContentHash.Compute(
            FrozenHashDomains.FrozenEvent,
            StructuredCanonicalWriter.WriteJson(withoutHash).AsSpan());
        var complete = DagEnvelope(eventType, payload, schemaVersion, hash);
        return (StructuredCanonicalWriter.WriteJson(complete), hash);
    }

    private static JsonElement DagEnvelope(
        string eventType,
        JsonElement payload,
        int schemaVersion,
        string? eventHash)
    {
        var envelope = new JsonObject();
        if (eventHash is not null)
        {
            envelope.Add("event_hash", eventHash);
        }

        envelope.Add("event_type", eventType);
        envelope.Add("payload", JsonNode.Parse(payload.GetRawText()));
        envelope.Add("schema_version", schemaVersion);
        return JsonSerializer.SerializeToElement(envelope);
    }

    private static bool HasExactFields(JsonElement value, IEnumerable<string> expected)
    {
        var actual = value.EnumerateObject().Select(static property => property.Name).ToArray();
        return actual.Length == actual.Distinct(StringComparer.Ordinal).Count()
            && actual.Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal));
    }
}
