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
                recordedPathsByIdentity,
                currentPathsByIdentity,
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
            .Select(node => FrozenLedgerCanonicalWriter.FreezePayload(candidateCatalog.Environment, node))
            .OrderBy(static payload => payload.CaseId, StringComparer.Ordinal)
            .Select(static payload => new FrozenLedgerDraft(
                "Freeze",
                FrozenLedgerCanonicalWriter.FreezeElement(payload)))
            .ToImmutableArray();
        return payloads;
    }

    internal static ImmutableArray<FrozenLedgerDraft> Revocation(
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
        return ImmutableArray.Create(new FrozenLedgerDraft(
            "Revoke",
            FrozenLedgerCanonicalWriter.RevokeElement(payload)));
    }

    private static string RevocationEvidenceRoot(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => item.RootFrozenNodeId.Value,
        RevocationEvidence.AllowedAxiomRetired item => item.RootFrozenNodeId.Value,
        RevocationEvidence.FormalContradictionCertificate item => item.RootFrozenNodeId.Value,
        RevocationEvidence.ContentAddressMismatch item => item.RootFrozenNodeId.Value,
        _ => throw new InvalidOperationException("unknown revocation evidence variant"),
    };

}

internal static class FrozenLedgerCanonicalWriter
{
    internal const int GenesisDagSchemaVersion = 2;
    internal const int CurrentDagSchemaVersion = 4;

    private static readonly string[] DagEnvelopeFields =
    [
        "event_hash", "event_type", "payload", "schema_version",
    ];

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
