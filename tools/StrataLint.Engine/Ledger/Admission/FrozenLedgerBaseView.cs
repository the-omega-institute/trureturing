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
    ImmutableArray<byte> RawBytes = default,
    JsonElement Root = default);

internal sealed record FrozenLedgerOrigin(string CommitOid, string TreeOid);

internal sealed class FrozenLedgerBaseView
{
    internal FrozenLedgerBaseView(
        FrozenLedgerOrigin origin,
        ImmutableArray<TrustedFrozenLedgerEvent> events,
        ImmutableDictionary<string, FrozenActiveEntry> activeByCase,
        ImmutableHashSet<string> allCaseIds,
        ImmutableHashSet<string> eventHashes,
        ImmutableHashSet<string> eventIdentities)
    {
        Origin = origin;
        Events = events;
        ActiveByCase = activeByCase;
        ActiveByPath = activeByCase.Values.ToImmutableDictionary(
            static entry => entry.Material.RepoPath);
        AllCaseIds = allCaseIds;
        EventHashes = eventHashes;
        EventIdentities = eventIdentities;
    }

    internal FrozenLedgerOrigin Origin { get; }

    internal ImmutableArray<TrustedFrozenLedgerEvent> Events { get; }

    internal ImmutableDictionary<string, FrozenActiveEntry> ActiveByCase { get; }

    internal ImmutableDictionary<RepoPath, FrozenActiveEntry> ActiveByPath { get; }

    internal ImmutableHashSet<string> AllCaseIds { get; }

    internal ImmutableHashSet<string> EventHashes { get; }

    internal ImmutableHashSet<string> EventIdentities { get; }

    internal int EventCount => Events.Length;

    internal FrozenLedgerConsistent ToWriterBaseline()
    {
        var typed = ImmutableArray.CreateBuilder<FrozenLedgerEvent>(Events.Length);
        for (var sequence = 0; sequence < Events.Length; sequence++)
        {
            var item = Events[sequence];
            var previousHash = sequence == 0
                ? FrozenLedgerCanonicalWriter.ZeroHash
                : Events[sequence - 1].EventHash;
            typed.Add(ProjectWriterEvent(item, sequence, previousHash));
        }

        var activeEntries = ActiveByCase;
        var revoked = Events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => FrozenLedgerAttestationChain.RequiredStringArray(
                item.Payload,
                "affected_frozen_node_ids"))
            .Select(FrozenNodeId.Create)
            .ToImmutableHashSet();
        var activeNodes = activeEntries.Values
            .Select(static entry => entry.Material)
            .OrderBy(static material => material.RepoPath.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        return FrozenLedgerConsistent.Create(
            ImmutableArray<byte>.Empty,
            typed.ToImmutable(),
            activeNodes,
            EventSetRoot(),
            corpusRoot: string.Empty,
            graphRoot: FrozenLedger.ComputeFrozenGraphRoot(activeNodes),
            activeEntries,
            AllCaseIds,
            revoked,
            syntaxStartSequence: Events.Length);
    }

    private static FrozenLedgerEvent ProjectWriterEvent(
        TrustedFrozenLedgerEvent item,
        int sequence,
        string previousHash) => item.EventType switch
        {
            "Genesis" => new FrozenLedgerEvent.Genesis(
                sequence,
                item.EventHash,
                previousHash,
                ReadGenesis(item.Payload)),
            "Freeze" => new FrozenLedgerEvent.Freeze(
                sequence,
                item.EventHash,
                previousHash,
                FrozenLedgerBaseViewReader.ReadFreeze(item.Payload, item.EventHash).Payload),
            "Revoke" => new FrozenLedgerEvent.Revoke(
                sequence,
                item.EventHash,
                previousHash,
                FrozenLedger.ReadTrustedRevoke(item.Payload)),
            _ => throw new InvalidOperationException(
                $"trusted frozen ledger contains unsupported event type {item.EventType}"),
        };

    internal string EventSetRoot(IEnumerable<string>? suffixEventHashes = null)
    {
        var material = JsonSerializer.SerializeToElement(new
        {
            event_hashes = Events.Select(static item => item.EventHash)
                .Concat(suffixEventHashes ?? [])
                .Order(StringComparer.Ordinal),
            schema = "frozen-event-set-v1",
        });
        return FrozenContentHash.Compute(
            FrozenHashDomains.FrozenEventSet,
            StructuredCanonicalWriter.WriteJson(material).AsSpan());
    }

    private static FrozenGenesisPayload ReadGenesis(JsonElement payload) => new(
        FrozenLedgerAttestationChain.RequiredString(payload, "generator_blob_oid"),
        FrozenLedgerAttestationChain.RequiredString(payload, "origin_commit_oid"),
        FrozenLedgerAttestationChain.RequiredString(payload, "origin_tree_oid"),
        payload.GetProperty("protocol_version").GetInt32(),
        FrozenLedgerAttestationChain.RequiredString(payload, "rule_catalog_root"));

}

internal static class FrozenLedgerAttestationChain
{
    internal static ImmutableArray<TrustedFrozenLedgerEvent> ActiveAttestations(
        ImmutableArray<TrustedFrozenLedgerEvent> events)
    {
        var revokedCases = events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => OptionalStringArray(item.Payload, "affected_case_ids"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var revokedNodes = events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => OptionalStringArray(
                item.Payload,
                "affected_frozen_node_ids"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        return events
            .Where(static item => item.EventType == "Freeze")
            .Where(item => (revokedCases.Count == 0
                    || !revokedCases.Contains(RequiredString(item.Payload, "case_id")))
                && (revokedNodes.Count == 0
                    || !revokedNodes.Contains(RequiredString(item.Payload, "frozen_node_id"))))
            .ToImmutableArray();
    }

    internal static string RequiredString(JsonElement value, string property) =>
        value.TryGetProperty(property, out var child) && child.ValueKind == JsonValueKind.String
            ? child.GetString()
                ?? throw new FormatException($"trusted frozen ledger field {property} is null")
            : throw new FormatException($"trusted frozen ledger field {property} is not a string");

    internal static ImmutableArray<string> RequiredStringArray(JsonElement value, string property)
    {
        if (!value.TryGetProperty(property, out var child) || child.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException($"trusted frozen ledger field {property} is not an array");
        }

        return child.EnumerateArray().Select(item => item.ValueKind == JsonValueKind.String
            ? item.GetString()
                ?? throw new FormatException($"trusted frozen ledger field {property} contains null")
            : throw new FormatException($"trusted frozen ledger field {property} contains a non-string"))
            .ToImmutableArray();
    }

    private static ImmutableArray<string> OptionalStringArray(JsonElement value, string property) =>
        value.TryGetProperty(property, out _)
            ? RequiredStringArray(value, property)
            : ImmutableArray<string>.Empty;
}

internal static class FrozenLedgerBaseViewReader
{
    internal static FrozenLedgerBaseView Read(RepositorySnapshot protectedBase)
    {
        ArgumentNullException.ThrowIfNull(protectedBase);
        var events = protectedBase.Files
            .Where(static item => FrozenLedgerChangeClassifier.IsAcceptedEventPath(item.Key.Value))
            .OrderBy(static item => item.Key.Value, StringComparer.Ordinal)
            .Select(static item => ReadEvent(item.Value))
            .ToImmutableArray();
        var genesis = events.Where(static item => item.EventType == "Genesis").ToArray();
        if (genesis.Length != 1)
        {
            throw new InvalidOperationException(
                "trusted protected-base frozen ledger does not contain exactly one Genesis event");
        }

        var origin = new FrozenLedgerOrigin(
            FrozenLedgerAttestationChain.RequiredString(genesis[0].Payload, "origin_commit_oid"),
            FrozenLedgerAttestationChain.RequiredString(genesis[0].Payload, "origin_tree_oid"));
        var activeByCase = FrozenLedgerAttestationChain.ActiveAttestations(events)
            .Select(ReadActiveEntry)
            .ToImmutableDictionary(static entry => entry.Payload.CaseId, StringComparer.Ordinal);
        var allCaseIds = events
            .Where(static item => item.EventType == "Freeze")
            .Select(static item => FrozenLedgerAttestationChain.RequiredString(item.Payload, "case_id"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        return new FrozenLedgerBaseView(
            origin,
            events,
            activeByCase,
            allCaseIds,
            events.Select(static item => item.EventHash).ToImmutableHashSet(StringComparer.Ordinal),
            events.Select(static item => item.Identity)
                .Concat(events.Where(static item => item.Payload.TryGetProperty("frozen_node_id", out _))
                    .Select(static item => FrozenLedgerAttestationChain.RequiredString(
                        item.Payload,
                        "frozen_node_id")))
                .ToImmutableHashSet(StringComparer.Ordinal));
    }

    internal static FrozenActiveEntry ReadActiveEntry(TrustedFrozenLedgerEvent head)
    {
        if (head.EventType != "Freeze")
        {
            throw new InvalidOperationException(
                $"trusted protected-base active event has unsupported type {head.EventType}");
        }

        return ReadFreeze(head.Payload, head.EventHash);
    }

    private static TrustedFrozenLedgerEvent ReadEvent(RepositoryFile file)
    {
        using var document = JsonDocument.Parse(file.RawBytes.ToArray());
        var root = document.RootElement;
        if (!FrozenLedgerCanonicalWriter.ReadTrustedDagEvent(
                root,
                out var identity,
                out var eventHash,
                out var message))
        {
            throw new FormatException(message);
        }

        var eventType = FrozenLedgerAttestationChain.RequiredString(root, "event_type");
        if (!root.TryGetProperty("payload", out var payload) || payload.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("trusted frozen ledger payload is not an object");
        }

        var payloadClone = payload.Clone();
        var rootClone = root.Clone();
        return new TrustedFrozenLedgerEvent(
            file.Path,
            eventType,
            eventHash,
            identity,
            payloadClone,
            file.RawBytes,
            rootClone);
    }

    internal static FrozenActiveEntry ReadFreeze(JsonElement payload, string eventHash)
    {
        var input = ReadInput(payload.GetProperty("input"));
        var path = ReadPath(input.DescriptorSelector);
        var declarations = ReadDeclarations(payload.GetProperty("declaration_statement_ids"));
        var statement = StatementId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "statement_id"));
        var witness = WitnessId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "witness_id"));
        var frozen = FrozenNodeId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "frozen_node_id"));
        var prerequisites = ReadFrozenNodeIds(payload, "prerequisite_frozen_node_ids");
        var axiomClosure = ReadOptionalAxiomClosure(payload);
        var freeze = new FrozenFreezePayload(
            FrozenLedgerAttestationChain.RequiredString(payload, "case_id"),
            declarations,
            frozen,
            input,
            prerequisites,
            statement,
            witness)
        {
            AxiomClosure = axiomClosure,
        };
        return new FrozenActiveEntry(
            ReadMaterial(
                path,
                declarations,
                statement,
                witness,
                frozen,
                prerequisites,
                axiomClosure.IsDefault ? ImmutableArray<string>.Empty : axiomClosure,
                input),
            freeze,
            eventHash,
            AxiomClosureKnown: !axiomClosure.IsDefault);
    }

    private static FrozenLedgerInput ReadInput(JsonElement value) => new(
        FrozenLedgerAttestationChain.RequiredString(value, "base_commit_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "base_tree_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "descriptor_blob_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "descriptor_selector"),
        FrozenLedgerAttestationChain.RequiredStringArray(value, "supporting_blob_oids"));

    private static ImmutableArray<FrozenDeclarationStatement> ReadDeclarations(JsonElement value)
    {
        if (value.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("trusted declaration_statement_ids is not an array");
        }

        return value.EnumerateArray().Select(item => new FrozenDeclarationStatement(
            FrozenLedgerAttestationChain.RequiredString(item, "declaration_name_key"),
            FrozenLedgerAttestationChain.RequiredString(item, "kind"),
            StatementId.Create(FrozenLedgerAttestationChain.RequiredString(item, "statement_id"))))
            .ToImmutableArray();
    }

    private static ImmutableArray<FrozenNodeId> ReadFrozenNodeIds(
        JsonElement value,
        string property) =>
        FrozenLedgerAttestationChain.RequiredStringArray(value, property)
            .Select(FrozenNodeId.Create)
            .ToImmutableArray();

    private static FrozenNodeMaterial ReadMaterial(
        RepoPath path,
        ImmutableArray<FrozenDeclarationStatement> declarations,
        StatementId statement,
        WitnessId witness,
        FrozenNodeId frozen,
        ImmutableArray<FrozenNodeId> prerequisites,
        ImmutableArray<string> axiomClosure,
        FrozenLedgerInput input) => new(
            path,
            declarations,
            statement,
            witness,
            frozen,
            prerequisites,
            axiomClosure,
            new FrozenModuleAttestation(path, input.DescriptorBlobOid)
            {
                BaseCommitOid = input.BaseCommitOid,
                BaseTreeOid = input.BaseTreeOid,
            });

    private static ImmutableArray<string> ReadOptionalAxiomClosure(JsonElement payload) =>
        payload.TryGetProperty("axiom_closure", out _)
            ? FrozenLedgerAttestationChain.RequiredStringArray(payload, "axiom_closure")
            : default;

    private static RepoPath ReadPath(string value) =>
        RepoPath.TryCreate(value, out var path)
            ? path
            : throw new FormatException("trusted protected-base ledger contains an undecodable path");
}
