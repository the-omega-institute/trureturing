using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public sealed record FrozenGenesisDescriptor(string GeneratorBlobOid, string RuleCatalogRoot);

public static class FrozenLedgerGenerator
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
            .OrderBy(static payload => payload.CaseClass, StringComparer.Ordinal)
            .ThenBy(static payload => payload.CaseId, StringComparer.Ordinal)
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
        foreach (var (path, active) in activeByPath)
        {
            if (candidateCatalog.ByPath.TryGetValue(path, out var candidate)
                && active.FrozenNodeId != candidate.FrozenNodeId)
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} changed identity; append Revoke before the replacement Freeze.");
            }
        }

        var payloads = candidateCatalog.ClosedNodes
            .Where(node => !activeByPath.ContainsKey(node.RepoPath))
            .Select(node => FrozenLedgerCanonicalWriter.FreezePayload(candidateCatalog.Environment, node))
            .OrderBy(static payload => payload.CaseClass, StringComparer.Ordinal)
            .ThenBy(static payload => payload.CaseId, StringComparer.Ordinal)
            .Select(static payload => (Type: "Freeze", Payload: FrozenLedgerCanonicalWriter.FreezeElement(payload)))
            .ToImmutableArray();
        return Append(baseline, payloads);
    }

    public static ImmutableArray<byte> AppendReattestation(
        FrozenLedgerConsistent baseline,
        string caseId,
        FrozenLedgerInput input)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(caseId);
        ArgumentNullException.ThrowIfNull(input);
        if (!baseline.ActiveEntries.TryGetValue(caseId, out var entry))
        {
            throw new ArgumentException("Reattest case is not active.", nameof(caseId));
        }

        var payload = new FrozenReattestPayload(
            caseId,
            input,
            entry.Payload.InputFingerprint,
            entry.LastAttestationEventHash,
            entry.Payload.SemanticReceipt);
        return Append(
            baseline,
            ImmutableArray.Create(("Reattest", FrozenLedgerCanonicalWriter.ReattestElement(payload))));
    }

    public static ImmutableArray<byte> AppendReattestation(
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog candidateCatalog)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidateCatalog);
        var activeByPath = baseline.ActiveEntries.Values.ToDictionary(
            static entry => entry.Material.RepoPath);
        var payloads = ImmutableArray.CreateBuilder<(string Type, JsonElement Payload)>();
        foreach (var (path, entry) in activeByPath.OrderBy(
            static item => item.Key.Value,
            StringComparer.Ordinal))
        {
            if (!candidateCatalog.ByPath.TryGetValue(path, out var candidate))
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} is no longer Closed; Reattest cannot change truth state.");
            }

            if (entry.Payload.StatementId != candidate.StatementId
                || !entry.Payload.DeclarationStatementIds.SequenceEqual(candidate.DeclarationStatementIds))
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} statement identity changed; Reattest is forbidden.");
            }

            if (entry.Material.FrozenNodeId == candidate.FrozenNodeId
                && entry.Payload.Input.DescriptorBlobOid == candidate.Attestation.SourceBlobOid)
            {
                continue;
            }

            var input = FrozenLedgerCanonicalWriter.FreezePayload(
                candidateCatalog.Environment,
                candidate).Input;
            var payload = ExtendedReattestPayload(entry.Payload.CaseId, entry, candidate, input);
            payloads.Add(("Reattest", FrozenLedgerCanonicalWriter.ReattestElement(payload)));
        }

        return Append(baseline, payloads.ToImmutable());
    }

    private static FrozenReattestPayload ExtendedReattestPayload(
        string caseId,
        FrozenActiveEntry entry,
        FrozenNodeMaterial material,
        FrozenLedgerInput input) =>
        new(
            caseId,
            material.DeclarationStatementIds,
            material.FrozenNodeId,
            input,
            material.WitnessId.Value,
            material.PrerequisiteFrozenNodeIds,
            entry.LastAttestationEventHash,
            material.FrozenNodeId.Value,
            material.StatementId,
            material.WitnessId);

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
            rootCases,
            plan.RootFrozenNodeIds);
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
            "active-frozen",
            CaseId(node.FrozenNodeId),
            node.DeclarationStatementIds,
            "admission",
            new FrozenExpectedVerdict(
                ImmutableArray.Create("admit"),
                "none",
                ImmutableArray<FrozenExpectedDiagnostic>.Empty),
            node.FrozenNodeId,
            new FrozenLedgerInput(
                node.Attestation.BaseCommitOid ?? environment.OriginCommitOid,
                node.Attestation.BaseTreeOid ?? environment.OriginTreeOid,
                node.Attestation.SourceBlobOid,
                node.RepoPath.Value,
                "repository-snapshot-v1",
                supporting),
            node.WitnessId.Value,
            node.RepoPath,
            node.PrerequisiteFrozenNodeIds,
            node.FrozenNodeId.Value,
            node.StatementId,
            nameof(TruthState.Closed),
            node.WitnessId);
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

    internal static JsonElement FreezeElement(FrozenFreezePayload payload) =>
        JsonSerializer.SerializeToElement(new
        {
            case_class = payload.CaseClass,
            case_id = payload.CaseId,
            declaration_statement_ids = payload.DeclarationStatementIds.Select(static declaration => new
            {
                declaration_name_key = declaration.DeclarationNameKey,
                kind = declaration.Kind,
                statement_id = declaration.StatementId.Value,
            }),
            evaluation = payload.Evaluation,
            expected = ExpectedElement(payload.Expected),
            frozen_node_id = payload.FrozenNodeId.Value,
            input = InputElement(payload.Input),
            input_fingerprint = payload.InputFingerprint,
            node_path = payload.NodePath.Value,
            prerequisite_frozen_node_ids = payload.PrerequisiteFrozenNodeIds.Select(static id => id.Value),
            semantic_receipt = payload.SemanticReceipt,
            statement_id = payload.StatementId.Value,
            truth_state = payload.TruthState,
            witness_id = payload.WitnessId.Value,
        });

    internal static JsonElement ExpectedElement(FrozenExpectedVerdict expected) =>
        JsonSerializer.SerializeToElement(new
        {
            allowed_dispositions = expected.AllowedDispositions,
            diagnostic_match = expected.DiagnosticMatch,
            required_diagnostics = expected.RequiredDiagnostics.Select(static diagnostic => new
            {
                message_sha256 = diagnostic.MessageSha256,
                path = diagnostic.Path,
                rule_id = diagnostic.RuleId,
            }),
        });

    internal static JsonElement InputElement(FrozenLedgerInput input) =>
        JsonSerializer.SerializeToElement(new
        {
            base_commit_oid = input.BaseCommitOid,
            base_tree_oid = input.BaseTreeOid,
            descriptor_blob_oid = input.DescriptorBlobOid,
            descriptor_selector = input.DescriptorSelector,
            materializer = input.Materializer,
            supporting_blob_oids = input.SupportingBlobOids,
        });

    internal static JsonElement ReattestElement(FrozenReattestPayload payload)
    {
        if (payload.IsLegacyFormat)
        {
            return JsonSerializer.SerializeToElement(new
            {
                case_id = payload.CaseId,
                input = InputElement(payload.Input),
                input_fingerprint = payload.InputFingerprint,
                previous_attestation_event_hash = payload.PreviousAttestationEventHash,
                semantic_receipt = payload.SemanticReceipt,
            });
        }

        if (!payload.IsExtendedFormat)
        {
            throw new InvalidOperationException(
                "Reattest payload must use either the legacy or extended field set.");
        }

        var frozenNodeId = payload.FrozenNodeId
            ?? throw new InvalidOperationException("Extended Reattest is missing frozen_node_id.");
        var statementId = payload.StatementId
            ?? throw new InvalidOperationException("Extended Reattest is missing statement_id.");
        var witnessId = payload.WitnessId
            ?? throw new InvalidOperationException("Extended Reattest is missing witness_id.");
        return JsonSerializer.SerializeToElement(new
        {
            case_id = payload.CaseId,
            declaration_statement_ids = payload.DeclarationStatementIds.Select(static declaration => new
            {
                declaration_name_key = declaration.DeclarationNameKey,
                kind = declaration.Kind,
                statement_id = declaration.StatementId.Value,
            }),
            frozen_node_id = frozenNodeId.Value,
            input = InputElement(payload.Input),
            input_fingerprint = payload.InputFingerprint,
            prerequisite_frozen_node_ids = payload.PrerequisiteFrozenNodeIds.Select(static id => id.Value),
            previous_attestation_event_hash = payload.PreviousAttestationEventHash,
            semantic_receipt = payload.SemanticReceipt,
            statement_id = statementId.Value,
            witness_id = witnessId.Value,
        });
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
            root_frozen_node_ids = payload.RootFrozenNodeIds.Select(static id => id.Value),
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
            expected_sha256 = item.ExpectedSha256,
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
        int sequence)
    {
        var withoutHash = JsonSerializer.SerializeToElement(new
        {
            event_type = eventType,
            payload,
            previous_hash = previousHash,
            schema_version = 1,
            sequence,
        });
        var hash = FrozenContentHash.Compute(
            FrozenHashDomains.FrozenEvent,
            StructuredCanonicalWriter.WriteJson(withoutHash).AsSpan());
        var complete = JsonSerializer.SerializeToElement(new
        {
            event_hash = hash,
            event_type = eventType,
            payload,
            previous_hash = previousHash,
            schema_version = 1,
            sequence,
        });
        return (StructuredCanonicalWriter.WriteJson(complete), hash);
    }
}
