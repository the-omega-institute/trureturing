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
        var revoked = Events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => FrozenLedgerAttestationChain.RequiredStringArray(
                item.Payload,
                "affected_frozen_node_ids"))
            .Select(FrozenNodeId.Create)
            .ToImmutableHashSet();
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
            revoked,
            EventHashes,
            Events.Length);
    }

    internal string EventSetRoot(IEnumerable<string>? suffixEventHashes = null)
        => FrozenEventSetRoot.Compute(
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

    private static readonly string[] GenesisV2Fields =
    [
        "generator_blob_oid", "origin_commit_oid", "origin_tree_oid", "protocol_version",
        "rule_catalog_root",
    ];

    private static readonly string[] FreezeV2Fields =
    [
        "case_class", "case_id", "declaration_statement_ids", "evaluation", "expected",
        "frozen_node_id", "input", "input_fingerprint", "node_path",
        "prerequisite_frozen_node_ids", "semantic_receipt", "statement_id", "truth_state",
        "witness_id",
    ];

    private static readonly string[] FreezeV3Fields =
    [
        "axiom_closure", "case_class", "case_id", "declaration_statement_ids", "evaluation",
        "expected", "frozen_node_id", "input", "input_fingerprint", "node_path",
        "prerequisite_frozen_node_ids", "semantic_receipt", "statement_id", "truth_state",
        "witness_id",
    ];

    private static readonly string[] FreezeV4Fields =
    [
        "axiom_closure", "case_id", "declaration_statement_ids", "frozen_node_id", "input",
        "prerequisite_frozen_node_ids", "statement_id", "witness_id",
    ];

    private static readonly string[] ReattestV2Fields =
    [
        "case_id", "declaration_statement_ids", "frozen_node_id", "input",
        "input_fingerprint", "prerequisite_frozen_node_ids",
        "previous_attestation_event_hash", "semantic_receipt", "statement_id", "witness_id",
    ];

    private static readonly string[] ReattestV3Fields =
    [
        "axiom_closure", "case_id", "input", "input_fingerprint",
        "previous_attestation_event_hash", "semantic_receipt",
    ];

    private static readonly string[] ReattestV4Fields =
    [
        "axiom_closure", "case_id", "declaration_statement_ids", "frozen_node_id", "input",
        "prerequisite_frozen_node_ids", "previous_attestation_event_hash", "statement_id",
        "witness_id",
    ];

    private static readonly string[] RevokeV4Fields =
    [
        "affected_case_ids", "affected_frozen_node_ids", "closure_hash", "evidence",
        "graph_root", "root_case_ids",
    ];

    private static readonly string[] HistoricalInputFields =
    [
        "base_commit_oid", "base_tree_oid", "descriptor_blob_oid", "descriptor_selector",
        "materializer", "supporting_blob_oids",
    ];

    private static readonly string[] CurrentInputFields =
    [
        "base_commit_oid", "base_tree_oid", "descriptor_blob_oid", "descriptor_selector",
        "supporting_blob_oids",
    ];

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
        var byHash = events.ToDictionary(static item => item.EventHash, StringComparer.Ordinal);

        // Validate every historical chain, including detached cycles and missing-parent fragments.
        foreach (var reattest in events.Where(static item => item.EventType == "Reattest"))
        {
            _ = ReadActiveEntry(reattest, byHash);
        }

        var revokedCases = events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => FrozenLedgerAttestationChain.OptionalStringArray(
                item.Payload,
                "affected_case_ids"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var revokedNodes = events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => FrozenLedgerAttestationChain.OptionalStringArray(
                item.Payload,
                "affected_frozen_node_ids"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var activeByCase = FrozenLedgerAttestationChain.ActiveAttestations(events)
            .Select(item => ReadActiveEntry(item, byHash))
            .Where(entry => !revokedCases.Contains(entry.Payload.CaseId)
                && !revokedNodes.Contains(entry.Material.FrozenNodeId.Value))
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

    internal static FrozenActiveEntry ReadActiveEntry(
        TrustedFrozenLedgerEvent head,
        IReadOnlyDictionary<string, TrustedFrozenLedgerEvent> byHash)
    {
        var chain = ImmutableArray.CreateBuilder<TrustedFrozenLedgerEvent>();
        var visiting = new HashSet<string>(StringComparer.Ordinal);
        var current = head;
        string? caseId = null;
        while (true)
        {
            if (!visiting.Add(current.EventHash))
            {
                throw new InvalidOperationException(
                    "trusted protected-base attestation chain contains a cycle");
            }

            if (current.EventType is not ("Freeze" or "Reattest"))
            {
                throw new InvalidOperationException(
                    $"trusted protected-base active event has unsupported type {current.EventType}");
            }

            var currentCaseId = FrozenLedgerAttestationChain.RequiredString(
                current.Payload,
                "case_id");
            caseId ??= currentCaseId;
            if (!string.Equals(caseId, currentCaseId, StringComparison.Ordinal))
            {
                throw new InvalidOperationException(
                    "trusted protected-base attestation chain changes case_id");
            }

            chain.Add(current);
            if (current.EventType == "Freeze")
            {
                break;
            }

            var previousHash = FrozenLedgerAttestationChain.RequiredString(
                current.Payload,
                "previous_attestation_event_hash");
            if (!byHash.TryGetValue(previousHash, out current!))
            {
                throw new InvalidOperationException(
                    "trusted protected-base attestation chain names an absent predecessor");
            }
        }

        var freeze = ReadFreeze(chain[^1].Payload, chain[^1].EventHash);
        var coordinate = chain.First(static item => item.EventType == "Freeze"
            || item.Payload.TryGetProperty("declaration_statement_ids", out _));
        var coordinateValues = coordinate.EventType == "Freeze"
            ? CoordinateValues.FromFreeze(ReadFreeze(coordinate.Payload, coordinate.EventHash).Payload)
            : CoordinateValues.FromReattest(ReadReattest(coordinate.Payload));
        var headInput = head.EventType == "Freeze"
            ? ReadFreeze(head.Payload, head.EventHash).Payload.Input
            : ReadReattest(head.Payload).Input;
        var axiomSource = chain.FirstOrDefault(static item =>
            item.Payload.TryGetProperty("axiom_closure", out _));
        var axiomClosure = axiomSource is null
            ? ImmutableArray<string>.Empty
            : FrozenLedgerAttestationChain.RequiredStringArray(
                axiomSource.Payload,
                "axiom_closure");
        var material = ReadMaterial(
            freeze.Material.RepoPath,
            coordinateValues.Declarations,
            coordinateValues.Statement,
            coordinateValues.Witness,
            coordinateValues.Frozen,
            coordinateValues.Prerequisites,
            axiomClosure,
            headInput);
        var payload = freeze.Payload with
        {
            AxiomClosure = axiomClosure,
            DeclarationStatementIds = coordinateValues.Declarations,
            FrozenNodeId = coordinateValues.Frozen,
            Input = headInput,
            PrerequisiteFrozenNodeIds = coordinateValues.Prerequisites,
            StatementId = coordinateValues.Statement,
            WitnessId = coordinateValues.Witness,
        };
        return new FrozenActiveEntry(
            material,
            payload,
            head.EventHash,
            AxiomClosureKnown: axiomSource is not null);
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

        ValidateTrustedPayload(eventType, schemaVersion, payload);
        return new TrustedFrozenLedgerEvent(
            file.Path,
            eventType,
            eventHash,
            eventHash,
            payload.Clone(),
            schemaVersion,
            file.RawBytes,
            root.Clone());
    }

    internal static void ValidateTrustedPayload(
        string eventType,
        int schemaVersion,
        JsonElement payload)
    {
        switch (eventType, schemaVersion)
        {
            case ("Genesis", 2):
                ConsumeGenesisV2(payload);
                return;
            case ("Freeze", 2):
                ConsumeFreeze(payload, FreezeV2Fields, hasAxiomClosure: false, legacy: true);
                return;
            case ("Freeze", 3):
                ConsumeFreeze(payload, FreezeV3Fields, hasAxiomClosure: true, legacy: true);
                return;
            case ("Freeze", 4):
                ConsumeFreeze(payload, FreezeV4Fields, hasAxiomClosure: true, legacy: false);
                return;
            case ("Reattest", 2):
                ConsumeReattest(payload, ReattestV2Fields, closureOnly: false);
                return;
            case ("Reattest", 3):
                ConsumeReattest(payload, ReattestV3Fields, closureOnly: true);
                return;
            case ("Reattest", 4):
                ConsumeReattest(payload, ReattestV4Fields, closureOnly: false);
                return;
            case ("Revoke", 4):
                RequireExactFields(payload, "trusted Revoke v4 payload", RevokeV4Fields);
                _ = FrozenLedger.ReadTrustedRevoke(payload);
                return;
            default:
                throw new FormatException(
                    $"trusted history has no decoder for {eventType} schema_version {schemaVersion}");
        }
    }

    private static void ConsumeGenesisV2(JsonElement payload)
    {
        RequireExactFields(payload, "trusted Genesis v2 payload", GenesisV2Fields);
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "generator_blob_oid");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "origin_commit_oid");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "origin_tree_oid");
        _ = FrozenLedgerAttestationChain.RequiredInteger(payload, "protocol_version");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "rule_catalog_root");
    }

    private static void ConsumeFreeze(
        JsonElement payload,
        string[] fields,
        bool hasAxiomClosure,
        bool legacy)
    {
        RequireExactFields(payload, "trusted Freeze payload", fields);
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "case_id");
        _ = ReadDeclarations(payload.GetProperty("declaration_statement_ids"));
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "frozen_node_id");
        ConsumeHistoricalInput(payload.GetProperty("input"));
        _ = FrozenLedgerAttestationChain.RequiredStringArray(
            payload,
            "prerequisite_frozen_node_ids");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "statement_id");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "witness_id");
        if (hasAxiomClosure)
        {
            _ = FrozenLedgerAttestationChain.RequiredStringArray(payload, "axiom_closure");
        }

        if (!legacy)
        {
            return;
        }

        _ = FrozenLedgerAttestationChain.RequiredString(payload, "case_class");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "evaluation");
        ConsumeLegacyExpected(payload.GetProperty("expected"));
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "node_path");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "truth_state");
    }

    private static void ConsumeReattest(
        JsonElement payload,
        string[] fields,
        bool closureOnly)
    {
        RequireExactFields(payload, "trusted Reattest payload", fields);
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "case_id");
        ConsumeHistoricalInput(payload.GetProperty("input"));
        _ = FrozenLedgerAttestationChain.RequiredString(
            payload,
            "previous_attestation_event_hash");
        if (closureOnly)
        {
            _ = FrozenLedgerAttestationChain.RequiredStringArray(payload, "axiom_closure");
            _ = FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint");
            _ = FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt");
            return;
        }

        _ = ReadDeclarations(payload.GetProperty("declaration_statement_ids"));
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "frozen_node_id");
        _ = FrozenLedgerAttestationChain.RequiredStringArray(
            payload,
            "prerequisite_frozen_node_ids");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "statement_id");
        _ = FrozenLedgerAttestationChain.RequiredString(payload, "witness_id");
        if (payload.TryGetProperty("axiom_closure", out _))
        {
            _ = FrozenLedgerAttestationChain.RequiredStringArray(payload, "axiom_closure");
        }

        if (payload.TryGetProperty("input_fingerprint", out _))
        {
            _ = FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint");
            _ = FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt");
        }
    }

    private static void ConsumeHistoricalInput(JsonElement input)
    {
        var fields = input.ValueKind == JsonValueKind.Object
            ? input.EnumerateObject().Select(static property => property.Name).ToArray()
            : [];
        if (MatchesExactFields(fields, HistoricalInputFields))
        {
            _ = FrozenLedgerAttestationChain.RequiredString(input, "materializer");
        }
        else if (!MatchesExactFields(fields, CurrentInputFields))
        {
            throw new FormatException(
                "trusted historical input has unknown, missing, or duplicate fields");
        }

        _ = FrozenLedgerAttestationChain.RequiredString(input, "base_commit_oid");
        _ = FrozenLedgerAttestationChain.RequiredString(input, "base_tree_oid");
        _ = FrozenLedgerAttestationChain.RequiredString(input, "descriptor_blob_oid");
        _ = FrozenLedgerAttestationChain.RequiredString(input, "descriptor_selector");
        _ = FrozenLedgerAttestationChain.RequiredStringArray(input, "supporting_blob_oids");
    }

    private static void ConsumeLegacyExpected(JsonElement expected)
    {
        RequireExactFields(
            expected,
            "trusted legacy expected result",
            ["allowed_dispositions", "diagnostic_match", "required_diagnostics"]);
        _ = FrozenLedgerAttestationChain.RequiredStringArray(expected, "allowed_dispositions");
        _ = FrozenLedgerAttestationChain.RequiredString(expected, "diagnostic_match");
        if (!expected.TryGetProperty("required_diagnostics", out var required)
            || required.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException(
                "trusted frozen ledger field required_diagnostics is not an array");
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

    internal static FrozenActiveEntry ReadFreeze(JsonElement payload, string eventHash)
    {
        var input = ReadInput(payload.GetProperty("input"));
        var path = ReadPath(payload.TryGetProperty("node_path", out _)
            ? FrozenLedgerAttestationChain.RequiredString(payload, "node_path")
            : input.DescriptorSelector);
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

    private static TrustedReattestProjection ReadReattest(JsonElement payload)
    {
        var input = ReadInput(payload.GetProperty("input"));
        var previous = FrozenLedgerAttestationChain.RequiredString(
            payload,
            "previous_attestation_event_hash");
        if (!payload.TryGetProperty("declaration_statement_ids", out var declarations))
        {
            return new TrustedReattestProjection(
                FrozenLedgerAttestationChain.RequiredString(payload, "case_id"),
                input,
                previous,
                default,
                null,
                null,
                ImmutableArray<FrozenNodeId>.Empty,
                null,
                ReadOptionalAxiomClosure(payload));
        }

        return new TrustedReattestProjection(
            FrozenLedgerAttestationChain.RequiredString(payload, "case_id"),
            input,
            previous,
            ReadDeclarations(declarations),
            FrozenNodeId.Create(FrozenLedgerAttestationChain.RequiredString(
                payload,
                "frozen_node_id")),
            StatementId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "statement_id")),
            ReadFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
            WitnessId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "witness_id")),
            ReadOptionalAxiomClosure(payload));
    }

    internal static FrozenLedgerInput? ReadTrustedAcceptedEventInput(
        string eventType,
        JsonElement payload) => eventType switch
        {
            "Genesis" or "Revoke" => null,
            "Freeze" or "Reattest" => ReadInput(payload.GetProperty("input")),
            _ => throw new FormatException($"Unknown trusted frozen event type {eventType}."),
        };

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

        return value.EnumerateArray().Select(item =>
        {
            RequireExactFields(
                item,
                "trusted declaration statement",
                ["declaration_name_key", "kind", "statement_id"]);
            return new FrozenDeclarationStatement(
                FrozenLedgerAttestationChain.RequiredString(item, "declaration_name_key"),
                FrozenLedgerAttestationChain.RequiredString(item, "kind"),
                StatementId.Create(FrozenLedgerAttestationChain.RequiredString(
                    item,
                    "statement_id")));
        }).ToImmutableArray();
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

    private sealed record TrustedReattestProjection(
        string CaseId,
        FrozenLedgerInput Input,
        string PreviousAttestationEventHash,
        ImmutableArray<FrozenDeclarationStatement> DeclarationStatementIds,
        FrozenNodeId? FrozenNodeId,
        StatementId? StatementId,
        ImmutableArray<FrozenNodeId> PrerequisiteFrozenNodeIds,
        WitnessId? WitnessId,
        ImmutableArray<string> AxiomClosure);

    private sealed record CoordinateValues(
        ImmutableArray<FrozenDeclarationStatement> Declarations,
        StatementId Statement,
        WitnessId Witness,
        FrozenNodeId Frozen,
        ImmutableArray<FrozenNodeId> Prerequisites)
    {
        internal static CoordinateValues FromFreeze(FrozenFreezePayload payload) => new(
            payload.DeclarationStatementIds,
            payload.StatementId,
            payload.WitnessId,
            payload.FrozenNodeId,
            payload.PrerequisiteFrozenNodeIds);

        internal static CoordinateValues FromReattest(TrustedReattestProjection payload) => new(
            payload.DeclarationStatementIds,
            payload.StatementId ?? throw new FormatException(
                "trusted extended Reattest is missing statement_id"),
            payload.WitnessId ?? throw new FormatException(
                "trusted extended Reattest is missing witness_id"),
            payload.FrozenNodeId ?? throw new FormatException(
                "trusted extended Reattest is missing frozen_node_id"),
            payload.PrerequisiteFrozenNodeIds);
    }
}
