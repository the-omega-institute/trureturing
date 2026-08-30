using System.Collections.Immutable;
using System.Text.Json;
using Trureturing.Truth;

namespace StrataLint.Engine;

internal sealed record TrustedFrozenLedgerEvent(
    RepoPath SourcePath,
    string EventType,
    string EventHash,
    string Identity,
    JsonElement Payload,
    int SchemaVersion,
    FrozenFreezePayload? FreezePayload,
    string? PreviousEventHash,
    ImmutableArray<byte> RawBytes = default,
    JsonElement Root = default);

internal sealed class FrozenLedgerBaseView
{
    internal FrozenLedgerBaseView(
        ImmutableArray<TrustedFrozenLedgerEvent> events,
        ImmutableDictionary<string, FrozenActiveEntry> activeByCase,
        ImmutableHashSet<string> eventHashes,
        ImmutableHashSet<string> eventIdentities)
    {
        Events = events;
        ActiveByCase = activeByCase;
        ActiveByPath = activeByCase.Values.ToImmutableDictionary(
            static entry => entry.Material.RepoPath);
        AllCaseIds = activeByCase.Keys.ToImmutableHashSet(StringComparer.Ordinal);
        EventHashes = eventHashes;
        EventIdentities = eventIdentities;
    }

    internal ImmutableArray<TrustedFrozenLedgerEvent> Events { get; }

    internal ImmutableDictionary<string, FrozenActiveEntry> ActiveByCase { get; }

    internal ImmutableDictionary<RepoPath, FrozenActiveEntry> ActiveByPath { get; }

    internal ImmutableHashSet<string> AllCaseIds { get; }

    internal ImmutableHashSet<string> EventHashes { get; }

    internal ImmutableHashSet<string> EventIdentities { get; }

    internal int EventCount => Events.Length;

    internal FrozenLedgerConsistent ToWriterBaseline()
    {
        var activeNodes = ActiveByCase.Values
            .Select(static entry => entry.Material)
            .OrderBy(static material => material.RepoPath.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        return FrozenLedgerConsistent.Create(
            activeNodes,
            EventSetRoot(),
            corpusRoot: string.Empty,
            graphRoot: FrozenLedger.ComputeFrozenGraphRoot(activeNodes),
            ActiveByCase,
            AllCaseIds,
            EventHashes,
            Events.Length);
    }

    internal string EventSetRoot(IEnumerable<string>? suffixEventHashes = null) =>
        FrozenEventSetRoot.Compute(
            Events.Select(static item => item.EventHash).Concat(suffixEventHashes ?? []));
}

internal static class FrozenEventSetRoot
{
    internal static string Compute(IEnumerable<string> eventHashes)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            event_hashes = eventHashes.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal),
            schema = "frozen-event-set-v1",
        });
        return FrozenContentHash.Compute(
            FrozenHashDomains.FrozenEventSet,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
    }
}

internal static class FrozenLedgerBaseViewReader
{
    private static readonly string[] EnvelopeFields =
    [
        "event_hash", "event_type", "payload", "schema_version",
    ];

    private static readonly string[] FreezeV5Fields =
    [
        "declaration_statement_ids", "descriptor_selector",
        "prerequisite_frozen_node_ids", "statement_id",
    ];

    private static readonly string[] ReanchorV5Fields =
    [
        "declaration_statement_ids", "descriptor_selector",
        "prerequisite_frozen_node_ids", "previous_event_hash", "statement_id",
    ];



    internal static FrozenLedgerBaseView Read(RepositorySnapshot protectedBase)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        var events = protectedBase.Files
            .Where(static item => FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key.Value))
            .OrderBy(static item => item.Key.Value, StringComparer.Ordinal)
            .Select(static item => ReadEvent(item.Value))
            .ToImmutableArray();
        var entries = events
            .Where(static item => item.EventType == "Freeze")
            .Select(ReadFreeze)
            .ToImmutableArray();

        RequireUnique(entries.Select(static entry => entry.Material.RepoPath.Value), "descriptor_selector");
        RequireUnique(entries.Select(static entry => entry.Material.FrozenNodeId.Value), "frozen node identity");
        RequireUnique(events.Select(static item => item.EventHash), "event_hash");

        var activeByCase = entries.ToDictionary(
            static entry => FrozenLedgerCanonicalWriter.CaseId(
                entry.Material.RepoPath,
                entry.Material.StatementId),
            StringComparer.Ordinal);
        ApplyReanchors(
            activeByCase,
            events.Where(static item => item.EventType == "Reanchor").ToImmutableArray());
        RequireUnique(
            activeByCase.Values.Select(static entry => entry.Material.FrozenNodeId.Value),
            "active frozen node identity");
        return new FrozenLedgerBaseView(
            events,
            activeByCase.ToImmutableDictionary(StringComparer.Ordinal),
            events.Select(static item => item.EventHash).ToImmutableHashSet(StringComparer.Ordinal),
            events.Select(static item => item.Identity)
                .Concat(events.Select(ReadFreeze).Select(static entry => entry.Material.FrozenNodeId.Value))
                .ToImmutableHashSet(StringComparer.Ordinal));
    }

    internal static TrustedFrozenLedgerEvent ReadEvent(RepositoryFile file)
    {
        using var document = JsonDocument.Parse(file.RawBytes.ToArray());
        var root = document.RootElement;
        RequireExactFields(root, "trusted history event envelope", EnvelopeFields);
        var eventType = FrozenLedgerAttestationChain.RequiredString(root, "event_type");
        var eventHash = FrozenLedgerAttestationChain.RequiredString(root, "event_hash");
        var schemaVersion = FrozenLedgerAttestationChain.RequiredInteger(root, "schema_version");
        if (!root.TryGetProperty("payload", out var payload) || payload.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("trusted frozen ledger payload is not an object");
        }

        var freezePayload = ValidateTrustedPayload(
            eventType,
            schemaVersion,
            payload,
            out var previousEventHash);
        if (!FrozenHashSyntax.IsSha256(eventHash))
        {
            throw new FormatException("trusted frozen ledger event_hash is malformed");
        }

        return new TrustedFrozenLedgerEvent(
            file.Path,
            eventType,
            eventHash,
            FrozenLedgerCanonicalWriter.EventIdentity(eventHash),
            payload.Clone(),
            schemaVersion,
            freezePayload,
            previousEventHash,
            file.RawBytes,
            root.Clone());
    }

    internal static FrozenFreezePayload ValidateTrustedPayload(
        string eventType,
        int schemaVersion,
        JsonElement payload,
        out string? previousEventHash)
    {
        if (schemaVersion != FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion)
        {
            throw new FormatException(
                $"trusted history has no decoder for {eventType} schema_version {schemaVersion}");
        }

        switch (eventType)
        {
            case "Freeze":
                RequireExactFields(payload, "trusted Freeze v5 payload", FreezeV5Fields);
                previousEventHash = null;
                break;
            case "Reanchor":
                RequireExactFields(payload, "trusted Reanchor v5 payload", ReanchorV5Fields);
                previousEventHash = FrozenLedgerAttestationChain.RequiredString(
                    payload,
                    "previous_event_hash");
                if (!FrozenHashSyntax.IsSha256(previousEventHash))
                {
                    throw new FormatException("trusted Reanchor previous_event_hash is malformed");
                }
                break;
            default:
                throw new FormatException($"trusted history has no decoder for {eventType} schema_version {schemaVersion}");
        }

        return DecodeFreezePayload(payload, schemaVersion);
    }

    internal static FrozenFreezePayload DecodeFreezePayload(
        JsonElement payload,
        int schemaVersion)
    {
        var path = ReadDescriptorPath(payload, schemaVersion);
        var declarations = ReadDeclarations(payload.GetProperty("declaration_statement_ids"));
        var statementValue = FrozenLedgerAttestationChain.RequiredString(payload, "statement_id");
        if (!FrozenHashSyntax.IsSha256(statementValue))
        {
            throw new FormatException("trusted Freeze statement_id is malformed");
        }

        var prerequisiteValues = FrozenLedgerAttestationChain.RequiredStringArray(
            payload,
            "prerequisite_frozen_node_ids");
        foreach (var prerequisite in prerequisiteValues)
        {
            if (!FrozenHashSyntax.IsSha256(prerequisite))
            {
                throw new FormatException("trusted Freeze prerequisite identity is malformed");
            }
        }

        return new FrozenFreezePayload(
            path.Value,
            declarations,
            prerequisiteValues.Select(FrozenNodeId.Create).ToImmutableArray(),
            StatementId.Create(statementValue));
    }

    internal static FrozenActiveEntry ReadFreeze(TrustedFrozenLedgerEvent item)
    {
        var freeze = item.FreezePayload
            ?? throw new FormatException(
                "trusted history event does not contain an active Freeze identity");
        var path = RepoPath.CreateKnown(freeze.DescriptorSelector);
        var frozenNodeId = FrozenContentAddress.ComputeFrozenNodeId(
            path,
            freeze.StatementId,
            freeze.PrerequisiteFrozenNodeIds);
        var material = new FrozenNodeMaterial(
            path,
            freeze.DeclarationStatementIds,
            freeze.StatementId,
            frozenNodeId,
            freeze.PrerequisiteFrozenNodeIds,
            ImmutableArray<string>.Empty);
        return new FrozenActiveEntry(
            material,
            freeze,
            item.EventHash,
            item.EventType);
    }

    private static void ApplyReanchors(
        Dictionary<string, FrozenActiveEntry> active,
        ImmutableArray<TrustedFrozenLedgerEvent> reanchors)
    {
        var remaining = reanchors.OrderBy(static item => item.EventHash, StringComparer.Ordinal).ToList();
        while (remaining.Count > 0)
        {
            var index = remaining.FindIndex(item =>
            {
                var payload = item.FreezePayload!;
                return active.TryGetValue(payload.CaseId, out var current)
                    && string.Equals(current.EventHash, item.PreviousEventHash, StringComparison.Ordinal);
            });
            if (index < 0)
            {
                throw new FormatException(
                    "trusted Reanchor chain does not extend the uniquely current active event");
            }

            var item = remaining[index];
            var reanchor = item.FreezePayload!;
            var current = active[reanchor.CaseId];
            FrozenLedger.ValidateReanchorTransition(
                current,
                reanchor,
                item.PreviousEventHash!);
            active[reanchor.CaseId] = ReadFreeze(item);
            remaining.RemoveAt(index);
        }
    }




    private static RepoPath ReadDescriptorPath(JsonElement payload, int schemaVersion)
    {
        var descriptorContainer = schemaVersion == FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion
            ? payload
            : payload.GetProperty("input");
        var value = FrozenLedgerAttestationChain.RequiredString(
            descriptorContainer,
            "descriptor_selector");
        return RepoPath.TryCreate(value, out var path)
            ? path
            : throw new FormatException("trusted Freeze descriptor_selector is not a canonical path");
    }

    private static ImmutableArray<FrozenDeclarationStatement> ReadDeclarations(JsonElement value)
    {
        if (value.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("trusted declaration_statement_ids is not an array");
        }

        var declarations = value.EnumerateArray().Select(item =>
        {
            RequireExactFields(
                item,
                "trusted declaration statement",
                ["declaration_name_key", "kind", "statement_id"]);
            var statement = FrozenLedgerAttestationChain.RequiredString(item, "statement_id");
            if (!FrozenHashSyntax.IsSha256(statement))
            {
                throw new FormatException("trusted declaration statement_id is malformed");
            }

            return new FrozenDeclarationStatement(
                FrozenLedgerAttestationChain.RequiredString(item, "declaration_name_key"),
                FrozenLedgerAttestationChain.RequiredString(item, "kind"),
                StatementId.Create(statement));
        }).ToImmutableArray();
        if (!declarations.SequenceEqual(
                declarations.OrderBy(static item => item.DeclarationNameKey, StringComparer.Ordinal)
                    .ThenBy(static item => item.Kind, StringComparer.Ordinal)
                    .ThenBy(static item => item.StatementId.Value, StringComparer.Ordinal))
            || declarations.Select(static item => item.DeclarationNameKey)
                .Distinct(StringComparer.Ordinal).Count() != declarations.Length)
        {
            throw new FormatException(
                "trusted declaration_statement_ids are not unique and canonically ordered");
        }

        return declarations;
    }

    private static void RequireUnique(IEnumerable<string> values, string label)
    {
        var materialized = values.ToArray();
        if (materialized.Distinct(StringComparer.Ordinal).Count() != materialized.Length)
        {
            throw new FormatException($"trusted frozen ledger contains duplicate {label}");
        }
    }

    private static void RequireExactFields(
        JsonElement value,
        string label,
        IEnumerable<string> expected)
    {
        if (value.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException($"{label} is not an object");
        }

        var actual = value.EnumerateObject().Select(static property => property.Name).ToArray();
        if (!MatchesExactFields(actual, expected))
        {
            throw new FormatException($"{label} has unknown, missing, or duplicate fields");
        }
    }

    private static bool MatchesExactFields(
        IReadOnlyCollection<string> actual,
        IEnumerable<string> expected) =>
        actual.Count == actual.Distinct(StringComparer.Ordinal).Count()
        && actual.Order(StringComparer.Ordinal).SequenceEqual(
            expected.Order(StringComparer.Ordinal),
            StringComparer.Ordinal);
}
