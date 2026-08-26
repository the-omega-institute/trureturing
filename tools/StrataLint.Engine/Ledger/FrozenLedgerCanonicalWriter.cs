using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;
using Trureturing.Truth;

namespace StrataLint.Engine;

public sealed record FrozenGenesisDescriptor(string GeneratorBlobOid, string RuleCatalogRoot);

public static partial class FrozenLedgerGenerator
{
    public static ImmutableArray<byte> GenerateGenesis(
        FrozenMaterialCatalog catalog,
        FrozenGenesisDescriptor descriptor)
    {
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(descriptor);
        if (!FrozenHashSyntax.IsGitOid(descriptor.GeneratorBlobOid)
            || !FrozenHashSyntax.IsSha256(descriptor.RuleCatalogRoot))
        {
            throw new FormatException("Genesis descriptor contains a malformed content address.");
        }

        var result = ImmutableArray.CreateBuilder<byte>();
        var previous = FrozenLedgerCanonicalWriter.ZeroHash;
        var genesis = FrozenLedgerCanonicalWriter.WriteEvent(
            "Genesis",
            FrozenLedgerCanonicalWriter.GenesisElement(catalog.Environment, descriptor),
            previous,
            0);
        result.AddRange(genesis.Bytes);
        previous = genesis.Hash;
        var freezes = catalog.ClosedNodes
            .Select(node => FrozenLedgerCanonicalWriter.FreezePayload(catalog.Environment, node))
            .OrderBy(static payload => payload.CaseId, StringComparer.Ordinal)
            .ToArray();
        for (var index = 0; index < freezes.Length; index++)
        {
            var line = FrozenLedgerCanonicalWriter.WriteEvent(
                "Freeze",
                FrozenLedgerCanonicalWriter.FreezeElement(freezes[index]),
                previous,
                index + 1);
            result.AddRange(line.Bytes);
            previous = line.Hash;
        }

        return result.ToImmutable();
    }

    public static ImmutableArray<byte> AppendMissingFreezes(
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog candidateCatalog)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidateCatalog);
        var activeByPath = baseline.ActiveEntries.Values.ToDictionary(
            static entry => entry.Material.RepoPath,
            static entry => entry.Material);
        return Append(baseline, MissingFreezeEvents(activeByPath, candidateCatalog));
    }

    private static ImmutableArray<(string Type, JsonElement Payload)> MissingFreezeEvents(
        IReadOnlyDictionary<RepoPath, FrozenNodeMaterial> activeByPath,
        FrozenMaterialCatalog candidateCatalog)
    {
        foreach (var (path, active) in activeByPath)
        {
            if (!candidateCatalog.ByPath.TryGetValue(path, out var candidate))
            {
                continue;
            }

            if (active.StatementId != candidate.StatementId
                || !active.DeclarationStatementIds.SequenceEqual(candidate.DeclarationStatementIds))
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} statement identity changed; append Revoke before rerunning ledger-append.");
            }

            if (active.FrozenNodeId != candidate.FrozenNodeId)
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} changed identity; append Revoke before rerunning ledger-append.");
            }
        }

        var payloads = candidateCatalog.ClosedNodes
            .Where(node => !activeByPath.ContainsKey(node.RepoPath))
            .Select(node => FrozenLedgerCanonicalWriter.FreezePayload(candidateCatalog.Environment, node))
            .OrderBy(static payload => payload.CaseId, StringComparer.Ordinal)
            .Select(static payload => (Type: "Freeze", Payload: FrozenLedgerCanonicalWriter.FreezeElement(payload)))
            .ToImmutableArray();
        return payloads;
    }

    public static ImmutableArray<byte> AppendRevocation(
        FrozenLedgerConsistent baseline,
        RevocationPlan plan)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(plan);
        if (plan.BaselineHeadHash != baseline.HeadHash)
        {
            throw new ArgumentException("Revocation plan is bound to a different ledger head.", nameof(plan));
        }

        var roots = plan.RootFrozenNodeIds.ToHashSet();
        var rootCases = baseline.ActiveEntries.Values
            .Where(entry => roots.Contains(entry.Material.FrozenNodeId))
            .Select(static entry => entry.Payload.CaseId)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var payload = new FrozenRevokePayload(
            plan.AffectedCaseIds,
            plan.AffectedFrozenNodeIds,
            plan.ClosureHash,
            plan.Evidence.Select(static item => item.Evidence)
                .OrderBy(RevocationEvidenceRoot, StringComparer.Ordinal)
                .ThenBy(static item => item.GetType().Name, StringComparer.Ordinal)
                .ToImmutableArray(),
            plan.GraphRoot,
            rootCases);
        return Append(
            baseline,
            ImmutableArray.Create(("Revoke", FrozenLedgerCanonicalWriter.RevokeElement(payload))));
    }

    private static string RevocationEvidenceRoot(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => item.RootFrozenNodeId.Value,
        RevocationEvidence.AllowedAxiomRetired item => item.RootFrozenNodeId.Value,
        RevocationEvidence.FormalContradictionCertificate item => item.RootFrozenNodeId.Value,
        RevocationEvidence.ContentAddressMismatch item => item.RootFrozenNodeId.Value,
        _ => throw new InvalidOperationException("unknown revocation evidence variant"),
    };

    private static ImmutableArray<byte> Append(
        FrozenLedgerConsistent baseline,
        ImmutableArray<(string Type, JsonElement Payload)> suffix)
    {
        var result = baseline.RawBytes.ToBuilder();
        var previous = baseline.HeadHash;
        var sequence = baseline.Events.Length;
        foreach (var item in suffix)
        {
            var line = FrozenLedgerCanonicalWriter.WriteEvent(item.Type, item.Payload, previous, sequence++);
            result.AddRange(line.Bytes);
            previous = line.Hash;
        }

        return result.ToImmutable();
    }
}

internal static class FrozenLedgerCanonicalWriter
{
    internal const int GenesisDagSchemaVersion = 2;
    internal const int CurrentDagSchemaVersion = 4;

    private static readonly string[] DagEnvelopeFields =
    [
        "event_hash", "event_type", "payload", "schema_version",
    ];

    internal const string ZeroHash = "sha256:0000000000000000000000000000000000000000000000000000000000000000";

    internal static string CaseId(FrozenNodeId id) => "active-frozen/" + id.Value[7..];

    internal static FrozenFreezePayload FreezePayload(
        FrozenEnvironmentAttestation environment,
        FrozenNodeMaterial node)
    {
        var supporting = new[]
        {
            environment.LeanToolchainBlobOid,
            environment.LakeManifestBlobOid,
        }.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
        return new FrozenFreezePayload(
            CaseId(node.FrozenNodeId),
            node.DeclarationStatementIds,
            node.FrozenNodeId,
            new FrozenLedgerInput(
                node.Attestation.BaseCommitOid ?? environment.OriginCommitOid,
                node.Attestation.BaseTreeOid ?? environment.OriginTreeOid,
                node.Attestation.SourceBlobOid,
                node.RepoPath.Value,
                supporting),
            node.PrerequisiteFrozenNodeIds,
            node.StatementId,
            node.WitnessId)
        {
            AxiomClosure = node.AxiomClosure,
        };
    }

    internal static JsonElement GenesisElement(
        FrozenEnvironmentAttestation environment,
        FrozenGenesisDescriptor descriptor) =>
        JsonSerializer.SerializeToElement(new
        {
            generator_blob_oid = descriptor.GeneratorBlobOid,
            origin_commit_oid = environment.OriginCommitOid,
            origin_tree_oid = environment.OriginTreeOid,
            protocol_version = 1,
            rule_catalog_root = descriptor.RuleCatalogRoot,
        });

    internal static JsonElement FreezeElement(FrozenFreezePayload payload)
    {
        var element = JsonSerializer.SerializeToElement(new
        {
            case_id = payload.CaseId,
            declaration_statement_ids = payload.DeclarationStatementIds.Select(static declaration => new
            {
                declaration_name_key = declaration.DeclarationNameKey,
                kind = declaration.Kind,
                statement_id = declaration.StatementId.Value,
            }),
            frozen_node_id = payload.FrozenNodeId.Value,
            input = InputElement(payload.Input),
            prerequisite_frozen_node_ids = payload.PrerequisiteFrozenNodeIds.Select(static id => id.Value),
            statement_id = payload.StatementId.Value,
            witness_id = payload.WitnessId.Value,
        });
        return WithAxiomClosure(element, payload.AxiomClosure);
    }

    internal static JsonElement InputElement(FrozenLedgerInput input) =>
        JsonSerializer.SerializeToElement(new
        {
            base_commit_oid = input.BaseCommitOid,
            base_tree_oid = input.BaseTreeOid,
            descriptor_blob_oid = input.DescriptorBlobOid,
            descriptor_selector = input.DescriptorSelector,
            supporting_blob_oids = input.SupportingBlobOids,
        });

    private static JsonElement WithAxiomClosure(
        JsonElement value,
        ImmutableArray<string> axiomClosure)
    {
        if (axiomClosure.IsDefault)
        {
            return value;
        }

        var result = JsonNode.Parse(value.GetRawText())!.AsObject();
        result.Add("axiom_closure", JsonSerializer.SerializeToNode(axiomClosure));
        return JsonSerializer.SerializeToElement(result);
    }

    internal static JsonElement RevokeElement(FrozenRevokePayload payload) =>
        JsonSerializer.SerializeToElement(new
        {
            affected_case_ids = payload.AffectedCaseIds,
            affected_frozen_node_ids = payload.AffectedFrozenNodeIds.Select(static id => id.Value),
            closure_hash = payload.ClosureHash,
            evidence = payload.Evidence.Select(EvidenceElement),
            graph_root = payload.GraphRoot,
            root_case_ids = payload.RootCaseIds,
        });

    internal static JsonElement EvidenceElement(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => JsonSerializer.SerializeToElement(new
        {
            evidence_type = nameof(RevocationEvidence.KernelWitnessFailure),
            failed_witness_id = item.FailedWitnessId.Value,
            receipt_blob_oid = item.ReceiptBlobOid,
            receipt_sha256 = item.ReceiptSha256,
            root_frozen_node_id = item.RootFrozenNodeId.Value,
        }),
        RevocationEvidence.AllowedAxiomRetired item => JsonSerializer.SerializeToElement(new
        {
            axiom_name = item.AxiomName,
            evidence_type = nameof(RevocationEvidence.AllowedAxiomRetired),
            receipt_blob_oid = item.ReceiptBlobOid,
            receipt_sha256 = item.ReceiptSha256,
            root_frozen_node_id = item.RootFrozenNodeId.Value,
        }),
        RevocationEvidence.FormalContradictionCertificate item => JsonSerializer.SerializeToElement(new
        {
            contradicted_statement_id = item.ContradictedStatementId.Value,
            evidence_type = nameof(RevocationEvidence.FormalContradictionCertificate),
            receipt_blob_oid = item.ReceiptBlobOid,
            receipt_sha256 = item.ReceiptSha256,
            root_frozen_node_id = item.RootFrozenNodeId.Value,
        }),
        RevocationEvidence.ContentAddressMismatch item => JsonSerializer.SerializeToElement(new
        {
            actual_sha256 = item.ActualSha256,
            evidence_type = nameof(RevocationEvidence.ContentAddressMismatch),
            receipt_blob_oid = item.ReceiptBlobOid,
            receipt_sha256 = item.ReceiptSha256,
            root_frozen_node_id = item.RootFrozenNodeId.Value,
        }),
        _ => throw new InvalidOperationException("unknown revocation evidence variant"),
    };

    internal static (ImmutableArray<byte> Bytes, string Hash) WriteEvent(
        string eventType,
        JsonElement payload,
        string previousHash,
        int sequence) =>
        WriteReplayEnvelope(eventType, payload, previousHash, sequence);

    internal static (ImmutableArray<byte> Bytes, string Hash) WriteDagEvent(
        string eventType,
        JsonElement payload,
        int? schemaVersion = null)
    {
        var expectedVersion = ExpectedDagSchemaVersion(eventType);
        var version = schemaVersion ?? expectedVersion;
        if (version != expectedVersion)
        {
            throw new ArgumentOutOfRangeException(
                nameof(schemaVersion),
                $"Content-addressed {eventType} schema_version must be {expectedVersion}.");
        }

        return WriteDagEnvelope(eventType, payload, version);
    }

    internal static bool ValidateDagEvent(
        JsonElement value,
        out string identity,
        out string eventHash,
        out string message) =>
        ReadDagEvent(value, validateRecordedHash: true, out identity, out eventHash, out message);

    internal static bool ReadTrustedDagEvent(
        JsonElement value,
        out string identity,
        out string eventHash,
        out string message) =>
        ReadDagEvent(value, validateRecordedHash: false, out identity, out eventHash, out message);

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
        var expectedVersion = ExpectedDagSchemaVersion(type);
        if (version != expectedVersion)
        {
            message = $"content-addressed {type} schema_version must be {expectedVersion}.";
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

    private static int ExpectedDagSchemaVersion(string eventType) =>
        eventType == "Genesis" ? GenesisDagSchemaVersion : CurrentDagSchemaVersion;

    private static (ImmutableArray<byte> Bytes, string Hash) WriteReplayEnvelope(
        string eventType,
        JsonElement payload,
        string previousHash,
        int sequence)
    {
        var withoutHash = ReplayEnvelope(eventType, payload, previousHash, sequence, null);
        var hash = FrozenContentHash.Compute(
            FrozenHashDomains.FrozenEvent,
            StructuredCanonicalWriter.WriteJson(withoutHash).AsSpan());
        var complete = ReplayEnvelope(eventType, payload, previousHash, sequence, hash);
        return (StructuredCanonicalWriter.WriteJson(complete), hash);
    }

    private static JsonElement ReplayEnvelope(
        string eventType,
        JsonElement payload,
        string previousHash,
        int sequence,
        string? eventHash)
    {
        var envelope = new JsonObject();
        if (eventHash is not null)
        {
            envelope.Add("event_hash", eventHash);
        }

        envelope.Add("event_type", eventType);
        envelope.Add("payload", JsonNode.Parse(payload.GetRawText()));
        envelope.Add("previous_hash", previousHash);
        envelope.Add("schema_version", 1);
        envelope.Add("sequence", sequence);
        return JsonSerializer.SerializeToElement(envelope);
    }

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
