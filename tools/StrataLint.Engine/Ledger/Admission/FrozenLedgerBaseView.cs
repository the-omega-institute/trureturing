using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal sealed record TrustedFrozenLedgerEvent(
    RepoPath SourcePath,
    string EventType,
    string EventHash,
    string Identity,
    JsonElement Payload);

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
}

internal static class FrozenLedgerAttestationChain
{
    internal static ImmutableArray<TrustedFrozenLedgerEvent> ActiveAttestations(
        ImmutableArray<TrustedFrozenLedgerEvent> events)
    {
        var superseded = events
            .Where(static item => item.EventType is "Reattest" or FrozenLedger.EnvironmentRecoordinateEventType)
            .Select(static item => RequiredString(item.Payload, "previous_attestation_event_hash"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        var revoked = events
            .Where(static item => item.EventType == "Revoke")
            .SelectMany(static item => RequiredStringArray(item.Payload, "affected_frozen_node_ids"))
            .ToImmutableHashSet(StringComparer.Ordinal);
        return events
            .Where(static item => item.EventType is "Freeze" or "Reattest"
                or FrozenLedger.EnvironmentRecoordinateEventType)
            .Where(item => !superseded.Contains(item.EventHash)
                && !revoked.Contains(item.Identity))
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
        var cache = new Dictionary<string, FrozenActiveEntry>(StringComparer.Ordinal);
        var visiting = new HashSet<string>(StringComparer.Ordinal);
        FrozenActiveEntry Project(TrustedFrozenLedgerEvent item)
        {
            if (cache.TryGetValue(item.EventHash, out var cached))
            {
                return cached;
            }

            if (!visiting.Add(item.EventHash))
            {
                throw new InvalidOperationException(
                    "trusted protected-base attestation chain contains a cycle");
            }

            FrozenActiveEntry projected;
            if (item.EventType == "Freeze")
            {
                projected = ReadFreeze(item.Payload, item.EventHash);
            }
            else
            {
                var previousHash = FrozenLedgerAttestationChain.RequiredString(
                    item.Payload,
                    "previous_attestation_event_hash");
                if (!byHash.TryGetValue(previousHash, out var previous))
                {
                    throw new InvalidOperationException(
                        "trusted protected-base attestation chain names an absent predecessor");
                }

                var entry = Project(previous);
                projected = item.EventType switch
                {
                    "Reattest" => FrozenLedger.ApplyReattest(
                        entry,
                        ReadReattest(item.Payload),
                        item.EventHash),
                    FrozenLedger.EnvironmentRecoordinateEventType =>
                        FrozenLedger.ApplyEnvironmentRecoordinate(
                            entry,
                            ReadEnvironmentRecoordinate(item.Payload),
                            item.EventHash),
                    _ => throw new InvalidOperationException(
                        $"trusted protected-base active event has unsupported type {item.EventType}"),
                };
            }

            visiting.Remove(item.EventHash);
            cache.Add(item.EventHash, projected);
            return projected;
        }

        var activeByCase = FrozenLedgerAttestationChain.ActiveAttestations(events)
            .Select(item => Project(item))
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
            events.Select(static item => item.Identity).ToImmutableHashSet(StringComparer.Ordinal));
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
        return new TrustedFrozenLedgerEvent(
            file.Path,
            eventType,
            eventHash,
            FrozenLedgerCanonicalWriter.EventIdentity(eventType, payloadClone, eventHash),
            payloadClone);
    }

    private static FrozenActiveEntry ReadFreeze(JsonElement payload, string eventHash)
    {
        var input = ReadInput(payload.GetProperty("input"));
        var path = ReadPath(FrozenLedgerAttestationChain.RequiredString(payload, "node_path"));
        var declarations = ReadDeclarations(payload.GetProperty("declaration_statement_ids"));
        var statement = StatementId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "statement_id"));
        var witness = WitnessId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "witness_id"));
        var frozen = FrozenNodeId.Create(
            FrozenLedgerAttestationChain.RequiredString(payload, "frozen_node_id"));
        var prerequisites = ReadFrozenNodeIds(payload, "prerequisite_frozen_node_ids");
        var freeze = new FrozenFreezePayload(
            FrozenLedgerAttestationChain.RequiredString(payload, "case_class"),
            FrozenLedgerAttestationChain.RequiredString(payload, "case_id"),
            declarations,
            FrozenLedgerAttestationChain.RequiredString(payload, "evaluation"),
            ReadExpected(payload.GetProperty("expected")),
            frozen,
            input,
            FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint"),
            path,
            prerequisites,
            FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt"),
            statement,
            FrozenLedgerAttestationChain.RequiredString(payload, "truth_state"),
            witness);
        return new FrozenActiveEntry(
            ReadMaterial(path, declarations, statement, witness, frozen, prerequisites, input),
            freeze,
            eventHash,
            AxiomClosureKnown: false);
    }

    private static FrozenReattestPayload ReadReattest(JsonElement payload)
    {
        var input = ReadInput(payload.GetProperty("input"));
        var caseId = FrozenLedgerAttestationChain.RequiredString(payload, "case_id");
        var fingerprint = FrozenLedgerAttestationChain.RequiredString(payload, "input_fingerprint");
        var previous = FrozenLedgerAttestationChain.RequiredString(
            payload,
            "previous_attestation_event_hash");
        var receipt = FrozenLedgerAttestationChain.RequiredString(payload, "semantic_receipt");
        if (!payload.TryGetProperty("declaration_statement_ids", out var declarations))
        {
            return new FrozenReattestPayload(caseId, input, fingerprint, previous, receipt);
        }

        return new FrozenReattestPayload(
            caseId,
            ReadDeclarations(declarations),
            FrozenNodeId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "frozen_node_id")),
            input,
            fingerprint,
            ReadFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
            previous,
            receipt,
            StatementId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "statement_id")),
            WitnessId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "witness_id")));
    }

    private static FrozenEnvironmentRecoordinatePayload ReadEnvironmentRecoordinate(JsonElement payload)
    {
        var declarations = payload.GetProperty("declaration_statement_ids");
        var environments = payload.GetProperty("environment");
        return new FrozenEnvironmentRecoordinatePayload(
            FrozenLedgerAttestationChain.RequiredString(payload, "case_id"),
            ReadDeclarations(declarations.GetProperty("new")),
            ReadDeclarations(declarations.GetProperty("old")),
            ReadEnvironmentPins(environments.GetProperty("new")),
            ReadEnvironmentPins(environments.GetProperty("old")),
            FrozenLedgerAttestationChain.RequiredString(payload, "equivalence_status"),
            FrozenLedgerAttestationChain.RequiredString(payload, "kernel_verdict"),
            FrozenLedgerAttestationChain.RequiredStringArray(payload, "new_axiom_closure"),
            FrozenNodeId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "new_frozen_node_id")),
            FrozenLedgerAttestationChain.RequiredStringArray(payload, "new_imports"),
            ReadInput(payload.GetProperty("new_input")),
            ReadFrozenNodeIds(payload, "new_prerequisite_frozen_node_ids"),
            StatementId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "new_statement_id")),
            WitnessId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "new_witness_id")),
            FrozenLedgerAttestationChain.RequiredStringArray(payload, "old_axiom_closure"),
            FrozenNodeId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "old_frozen_node_id")),
            FrozenLedgerAttestationChain.RequiredStringArray(payload, "old_imports"),
            ReadInput(payload.GetProperty("old_input")),
            ReadFrozenNodeIds(payload, "old_prerequisite_frozen_node_ids"),
            StatementId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "old_statement_id")),
            WitnessId.Create(FrozenLedgerAttestationChain.RequiredString(payload, "old_witness_id")),
            FrozenLedgerAttestationChain.RequiredString(payload, "previous_attestation_event_hash"),
            FrozenLedgerAttestationChain.RequiredString(payload, "source_sha256"));
    }

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
        FrozenLedgerInput input) => new(
            path,
            declarations,
            statement,
            witness,
            frozen,
            prerequisites,
            ImmutableArray<string>.Empty,
            new FrozenModuleAttestation(path, input.DescriptorBlobOid)
            {
                BaseCommitOid = input.BaseCommitOid,
                BaseTreeOid = input.BaseTreeOid,
            });

    private static RepoPath ReadPath(string value) =>
        RepoPath.TryCreate(value, out var path)
            ? path
            : throw new FormatException("trusted protected-base ledger contains an undecodable path");
}
