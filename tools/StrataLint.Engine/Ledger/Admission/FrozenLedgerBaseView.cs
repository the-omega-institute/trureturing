using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record TrustedFrozenLedgerEvent(
    RepoPath SourcePath,
    string EventType,
    string EventHash,
    string Identity,
    JsonElement Payload,
    int SchemaVersion = FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion,
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
        ImmutableHashSet<string> eventIdentities,
        int baseEventsFolded = 0)
    {
        Origin = origin;
        Events = events;
        ActiveByCase = activeByCase;
        ActiveByPath = activeByCase.Values.ToImmutableDictionary(
            static entry => entry.Material.RepoPath);
        AllCaseIds = allCaseIds;
        EventHashes = eventHashes;
        EventIdentities = eventIdentities;
        BaseEventsFolded = baseEventsFolded;
    }

    internal FrozenLedgerOrigin Origin { get; }

    internal ImmutableArray<TrustedFrozenLedgerEvent> Events { get; }

    internal ImmutableDictionary<string, FrozenActiveEntry> ActiveByCase { get; }

    internal ImmutableDictionary<RepoPath, FrozenActiveEntry> ActiveByPath { get; }

    internal ImmutableHashSet<string> AllCaseIds { get; }

    internal ImmutableHashSet<string> EventHashes { get; }

    internal ImmutableHashSet<string> EventIdentities { get; }

    internal int EventCount => Events.Length;

    internal int BaseEventsFolded { get; }

    internal FrozenLedgerConsistent ToWriterBaseline(FrozenLedgerSyntax syntax)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        if (syntax.Lines.Length != Events.Length)
        {
            throw new InvalidOperationException(
                "trusted frozen ledger projection and linear writer view have different event counts");
        }

        var byDagHash = Events.ToDictionary(static item => item.EventHash, StringComparer.Ordinal);
        var linearHashByDagHash = syntax.Lines.ToDictionary(
            static line => line.SourceDagEventHash
                ?? throw new InvalidOperationException(
                    "trusted frozen ledger linear view lost its content-addressed source hash"),
            static line => RequiredLinearString(line.Value, "event_hash"),
            StringComparer.Ordinal);
        var typed = syntax.Lines.Select(line =>
        {
            var sourceHash = line.SourceDagEventHash!;
            if (!byDagHash.TryGetValue(sourceHash, out var item))
            {
                throw new InvalidOperationException(
                    "trusted frozen ledger linear view names an absent content-addressed event");
            }

            var sequence = line.Value.GetProperty("sequence").GetInt32();
            var eventHash = RequiredLinearString(line.Value, "event_hash");
            var previousHash = RequiredLinearString(line.Value, "previous_hash");
            return item.EventType switch
            {
                "Genesis" => (FrozenLedgerEvent)new FrozenLedgerEvent.Genesis(
                    sequence,
                    eventHash,
                    previousHash,
                    ReadGenesis(item.Payload)),
                "Freeze" => new FrozenLedgerEvent.Freeze(
                    sequence,
                    eventHash,
                    previousHash,
                    FrozenLedgerBaseViewReader.ReadFreeze(item.Payload, eventHash).Payload),
                "Reattest" => new FrozenLedgerEvent.Reattest(
                    sequence,
                    eventHash,
                    previousHash,
                    FrozenLedgerBaseViewReader.ReadReattest(
                        item.Payload,
                        ReadActiveBefore(item, byDagHash).Payload)),
                FrozenLedger.SupersedeEventType => new FrozenLedgerEvent.Supersede(
                    sequence,
                    eventHash,
                    previousHash,
                    FrozenLedgerBaseViewReader.ReadSupersede(item.Payload)),
                "Revoke" => new FrozenLedgerEvent.Revoke(
                    sequence,
                    eventHash,
                    previousHash,
                    FrozenLedger.ReadTrustedRevoke(item.Payload)),
                _ => throw new InvalidOperationException(
                    $"trusted frozen ledger contains unsupported event type {item.EventType}"),
            };
        }).ToImmutableArray();
        var activeEntries = ActiveByCase.ToImmutableDictionary(
            static item => item.Key,
            item => item.Value with
            {
                LastAttestationEventHash = linearHashByDagHash[item.Value.LastAttestationEventHash],
            },
            StringComparer.Ordinal);
        var superseded = Events
            .Where(static item => item.EventType == FrozenLedger.SupersedeEventType)
            .Select(item => ReadActiveBefore(item, byDagHash).Material.FrozenNodeId)
            .ToImmutableHashSet();
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
            syntax.RawBytes,
            typed,
            activeNodes,
            syntax.Lines.Length == 0
                ? string.Empty
                : RequiredLinearString(syntax.Lines[^1].Value, "event_hash"),
            corpusRoot: string.Empty,
            graphRoot: FrozenLedger.ComputeFrozenGraphRoot(activeNodes),
            activeEntries,
            AllCaseIds,
            superseded,
            revoked);
    }

    private static FrozenActiveEntry ReadActiveBefore(
        TrustedFrozenLedgerEvent item,
        IReadOnlyDictionary<string, TrustedFrozenLedgerEvent> byHash)
    {
        var previousHash = FrozenLedgerAttestationChain.RequiredString(
            item.Payload,
            "previous_attestation_event_hash");
        return byHash.TryGetValue(previousHash, out var previous)
            ? FrozenLedgerBaseViewReader.ReadActiveEntry(previous, byHash)
            : throw new InvalidOperationException(
                "trusted Supersede names an absent predecessor");
    }

    private static FrozenGenesisPayload ReadGenesis(JsonElement payload) => new(
        FrozenLedgerAttestationChain.RequiredString(payload, "generator_blob_oid"),
        FrozenLedgerAttestationChain.RequiredString(payload, "origin_commit_oid"),
        FrozenLedgerAttestationChain.RequiredString(payload, "origin_tree_oid"),
        payload.GetProperty("protocol_version").GetInt32(),
        FrozenLedgerAttestationChain.RequiredString(payload, "rule_catalog_root"));

    private static string RequiredLinearString(JsonElement value, string property) =>
        FrozenLedgerAttestationChain.RequiredString(value, property);
}

internal static class FrozenLedgerAttestationChain
{
    internal static ImmutableArray<TrustedFrozenLedgerEvent> ActiveAttestations(
        ImmutableArray<TrustedFrozenLedgerEvent> events)
    {
        var superseded = events
            .Where(static item => item.EventType is "Reattest" or FrozenLedger.SupersedeEventType)
            .Select(static item => RequiredString(item.Payload, "previous_attestation_event_hash"))
            .ToImmutableHashSet(StringComparer.Ordinal);
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
            .Where(static item => item.EventType is "Freeze" or "Reattest"
                or FrozenLedger.SupersedeEventType)
            .Where(item => !superseded.Contains(item.EventHash)
                && (revokedCases.Count == 0
                    || !revokedCases.Contains(RequiredString(item.Payload, "case_id")))
                && (revokedNodes.Count == 0
                    || !revokedNodes.Contains(ActiveFrozenNodeId(item))))
            .ToImmutableArray();
    }

    private static string ActiveFrozenNodeId(TrustedFrozenLedgerEvent item) =>
        item.EventType switch
        {
            FrozenLedger.SupersedeEventType => RequiredString(item.Payload, "frozen_node_id"),
            "Reattest" when item.Payload.TryGetProperty("frozen_node_id", out _) =>
                RequiredString(item.Payload, "frozen_node_id"),
            "Reattest" => RequiredString(item.Payload, "semantic_receipt"),
            "Freeze" when item.Payload.TryGetProperty("frozen_node_id", out _) =>
                RequiredString(item.Payload, "frozen_node_id"),
            "Freeze" => item.Identity,
            _ => throw new InvalidOperationException(
                $"trusted protected-base attestation has unsupported type {item.EventType}"),
        };

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
        var byHash = events.ToDictionary(static item => item.EventHash, StringComparer.Ordinal);
        var activeByCase = FrozenLedgerAttestationChain.ActiveAttestations(events)
            .Select(item => ReadActiveEntry(item, byHash))
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
        while (true)
        {
            if (!visiting.Add(current.EventHash))
            {
                throw new InvalidOperationException(
                    "trusted protected-base attestation chain contains a cycle");
            }

            chain.Add(current);
            if (current.EventType == "Freeze")
            {
                break;
            }

            if (current.EventType is not ("Reattest" or FrozenLedger.SupersedeEventType))
            {
                throw new InvalidOperationException(
                    $"trusted protected-base active event has unsupported type {current.EventType}");
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
        var coordinate = chain.First(static item => item.EventType is "Freeze"
            or FrozenLedger.SupersedeEventType
            || item.Payload.TryGetProperty("declaration_statement_ids", out _));
        var axiomSource = chain.FirstOrDefault(static item =>
            item.Payload.TryGetProperty("axiom_closure", out _));
        var environmentSource = chain.FirstOrDefault(static item =>
            item.EventType == FrozenLedger.SupersedeEventType);
        return ReadProjectedEntry(
            freeze,
            head,
            coordinate,
            axiomSource,
            environmentSource);
    }

    private static FrozenActiveEntry ReadProjectedEntry(
        FrozenActiveEntry freeze,
        TrustedFrozenLedgerEvent head,
        TrustedFrozenLedgerEvent coordinate,
        TrustedFrozenLedgerEvent? axiomSource,
        TrustedFrozenLedgerEvent? environmentSource)
    {
        var coordinateValues = coordinate.EventType switch
        {
            "Freeze" => CoordinateValues.FromFreeze(ReadFreeze(
                coordinate.Payload,
                coordinate.EventHash).Payload),
            "Reattest" => CoordinateValues.FromReattest(ReadReattest(coordinate.Payload, freeze.Payload)),
            FrozenLedger.SupersedeEventType => CoordinateValues.FromSupersede(
                ReadSupersede(coordinate.Payload)),
            _ => throw new InvalidOperationException(
                $"trusted protected-base coordinate event has unsupported type {coordinate.EventType}"),
        };
        var headValues = head.EventType switch
        {
            "Freeze" => HeadValues.FromFreeze(ReadFreeze(head.Payload, head.EventHash).Payload),
            "Reattest" => HeadValues.FromReattest(ReadReattest(head.Payload, freeze.Payload)),
            FrozenLedger.SupersedeEventType => HeadValues.FromSupersede(ReadSupersede(head.Payload)),
            _ => throw new InvalidOperationException(
                $"trusted protected-base head event has unsupported type {head.EventType}"),
        };
        var axiomClosure = axiomSource is null
            ? ImmutableArray<string>.Empty
            : FrozenLedgerAttestationChain.RequiredStringArray(
                axiomSource.Payload,
                "axiom_closure");
        var path = freeze.Material.RepoPath;
        var material = ReadMaterial(
            path,
            coordinateValues.Declarations,
            coordinateValues.Statement,
            coordinateValues.Witness,
            coordinateValues.Frozen,
            coordinateValues.Prerequisites,
            axiomClosure,
            headValues.Input);
        var payload = freeze.Payload with
        {
            AxiomClosure = axiomClosure,
            DeclarationStatementIds = coordinateValues.Declarations,
            FrozenNodeId = coordinateValues.Frozen,
            Input = headValues.Input,
            InputFingerprint = headValues.InputFingerprint,
            PrerequisiteFrozenNodeIds = coordinateValues.Prerequisites,
            SemanticReceipt = headValues.SemanticReceipt,
            StatementId = coordinateValues.Statement,
            WitnessId = coordinateValues.Witness,
        };
        return new FrozenActiveEntry(
            material,
            payload,
            head.EventHash,
            AxiomClosureKnown: axiomSource is not null,
            Environment: environmentSource is null
                ? null
                : ReadSupersede(environmentSource.Payload).Environment);
    }

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

        internal static CoordinateValues FromReattest(FrozenReattestPayload payload) => new(
            payload.DeclarationStatementIds,
            payload.StatementId ?? throw new FormatException(
                "trusted extended Reattest is missing statement_id"),
            payload.WitnessId ?? throw new FormatException(
                "trusted extended Reattest is missing witness_id"),
            payload.FrozenNodeId ?? throw new FormatException(
                "trusted extended Reattest is missing frozen_node_id"),
            payload.PrerequisiteFrozenNodeIds);

        internal static CoordinateValues FromSupersede(FrozenSupersedePayload payload) => new(
            payload.DeclarationStatementIds,
            payload.StatementId,
            payload.WitnessId,
            payload.FrozenNodeId,
            payload.PrerequisiteFrozenNodeIds);
    }

    private sealed record HeadValues(
        FrozenLedgerInput Input,
        string InputFingerprint,
        string SemanticReceipt)
    {
        internal static HeadValues FromFreeze(FrozenFreezePayload payload) => new(
            payload.Input,
            payload.InputFingerprint,
            payload.SemanticReceipt);

        internal static HeadValues FromReattest(FrozenReattestPayload payload) => new(
            payload.Input,
            payload.InputFingerprint,
            payload.SemanticReceipt);

        internal static HeadValues FromSupersede(FrozenSupersedePayload payload) => new(
            payload.Input,
            payload.WitnessId.Value,
            payload.FrozenNodeId.Value);
    }

    private static TrustedFrozenLedgerEvent ReadEvent(RepositoryFile file)
    {
        using var document = JsonDocument.Parse(file.RawBytes.ToArray());
        var root = document.RootElement;
        var eventType = FrozenLedgerAttestationChain.RequiredString(root, "event_type");
        var eventHash = FrozenLedgerAttestationChain.RequiredString(root, "event_hash");
        if (!root.TryGetProperty("payload", out var payload) || payload.ValueKind != JsonValueKind.Object)
        {
            throw new FormatException("trusted frozen ledger payload is not an object");
        }

        var payloadClone = payload.Clone();
        var rootClone = root.Clone();
        var schemaVersion = root.GetProperty("schema_version").GetInt32();
        var identity = FrozenLedgerCanonicalWriter.EventIdentity(
            eventType,
            payload,
            eventHash,
            schemaVersion);
        return new TrustedFrozenLedgerEvent(
            file.Path,
            eventType,
            eventHash,
            identity,
            payloadClone,
            schemaVersion,
            file.RawBytes,
            rootClone);
    }

    internal static FrozenActiveEntry ReadFreeze(JsonElement payload, string eventHash)
    {
        var input = ReadInput(payload.GetProperty("input"));
        var currentShape = !payload.TryGetProperty("node_path", out _);
        var path = ReadPath(currentShape
            ? input.DescriptorSelector
            : FrozenLedgerAttestationChain.RequiredString(payload, "node_path"));
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
            currentShape
                ? "active-frozen"
                : FrozenLedgerAttestationChain.RequiredString(payload, "case_class"),
            FrozenLedgerAttestationChain.RequiredString(payload, "case_id"),
            declarations,
            currentShape
                ? "admission"
                : FrozenLedgerAttestationChain.RequiredString(payload, "evaluation"),
            currentShape
                ? new FrozenExpectedVerdict(
                    ImmutableArray.Create("admit"),
                    "none",
                    ImmutableArray<FrozenExpectedDiagnostic>.Empty)
                : ReadExpected(payload.GetProperty("expected")),
            frozen,
            input,
            currentShape
                ? witness.Value
                : FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint"),
            path,
            prerequisites,
            currentShape
                ? frozen.Value
                : FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt"),
            statement,
            currentShape
                ? nameof(TruthState.Closed)
                : FrozenLedgerAttestationChain.RequiredString(payload, "truth_state"),
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

    internal static FrozenReattestPayload ReadReattest(
        JsonElement payload,
        FrozenFreezePayload identitySource)
    {
        var input = ReadInput(payload.GetProperty("input"));
        var caseId = FrozenLedgerAttestationChain.RequiredString(payload, "case_id");
        var previous = FrozenLedgerAttestationChain.RequiredString(
            payload,
            "previous_attestation_event_hash");
        if (!payload.TryGetProperty("declaration_statement_ids", out var declarations))
        {
            var fingerprint = payload.TryGetProperty("input_fingerprint", out _)
                ? FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint")
                : identitySource.InputFingerprint;
            var receipt = payload.TryGetProperty("semantic_receipt", out _)
                ? FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt")
                : identitySource.SemanticReceipt;
            return new FrozenReattestPayload(caseId, input, fingerprint, previous, receipt)
            {
                AxiomClosure = ReadOptionalAxiomClosure(payload),
            };
        }

        var witness = WitnessId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "witness_id"));
        var frozen = FrozenNodeId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "frozen_node_id"));
        return new FrozenReattestPayload(
            caseId,
            ReadDeclarations(declarations),
            frozen,
            input,
            payload.TryGetProperty("input_fingerprint", out _)
                ? FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint")
                : witness.Value,
            ReadFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
            previous,
            payload.TryGetProperty("semantic_receipt", out _)
                ? FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt")
                : frozen.Value,
            StatementId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "statement_id")),
            witness)
        {
            AxiomClosure = ReadOptionalAxiomClosure(payload),
        };
    }

    internal static FrozenSupersedePayload ReadSupersede(JsonElement payload) => new(
        FrozenLedgerAttestationChain.RequiredStringArray(payload, "axiom_closure"),
        FrozenLedgerAttestationChain.RequiredString(payload, "case_id"),
        ReadDeclarations(payload.GetProperty("declaration_statement_ids")),
        ReadEnvironmentPins(payload.GetProperty("environment")),
        FrozenNodeId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "frozen_node_id")),
        ReadSupersedeInput(payload.GetProperty("input")),
        ReadFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
        FrozenLedgerAttestationChain.RequiredString(payload, "previous_attestation_event_hash"),
        StatementId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "statement_id")),
        WitnessId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "witness_id")));

    private static FrozenEnvironmentPins ReadEnvironmentPins(JsonElement value) => new(
        FrozenLedgerAttestationChain.RequiredString(value, "lake_manifest_blob_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "lakefile_blob_oid"),
        ReadPath(FrozenLedgerAttestationChain.RequiredString(value, "lakefile_path")),
        FrozenLedgerAttestationChain.RequiredString(value, "lean_toolchain_blob_oid"));

    private static FrozenLedgerInput ReadInput(JsonElement value) => new(
        FrozenLedgerAttestationChain.RequiredString(value, "base_commit_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "base_tree_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "descriptor_blob_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "descriptor_selector"),
        FrozenLedgerAttestationChain.RequiredString(value, "materializer"),
        FrozenLedgerAttestationChain.RequiredStringArray(value, "supporting_blob_oids"));

    private static FrozenLedgerInput ReadSupersedeInput(JsonElement value) => new(
        FrozenLedgerAttestationChain.RequiredString(value, "base_commit_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "base_tree_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "descriptor_blob_oid"),
        FrozenLedgerAttestationChain.RequiredString(value, "descriptor_selector"),
        FrozenLedgerAttestationChain.RequiredString(value, "materializer"),
        ImmutableArray<string>.Empty);

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

    private static FrozenExpectedVerdict ReadExpected(JsonElement value)
    {
        var diagnostics = value.GetProperty("required_diagnostics");
        if (diagnostics.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("trusted required_diagnostics is not an array");
        }

        return new FrozenExpectedVerdict(
            FrozenLedgerAttestationChain.RequiredStringArray(value, "allowed_dispositions"),
            FrozenLedgerAttestationChain.RequiredString(value, "diagnostic_match"),
            diagnostics.EnumerateArray().Select(item => new FrozenExpectedDiagnostic(
                FrozenLedgerAttestationChain.RequiredString(item, "message_sha256"),
                FrozenLedgerAttestationChain.RequiredString(item, "path"),
                FrozenLedgerAttestationChain.RequiredString(item, "rule_id")))
                .ToImmutableArray());
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
