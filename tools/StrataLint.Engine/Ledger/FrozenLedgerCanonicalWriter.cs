using System.Collections.Immutable;
using System.Text.Json;
using System.Text.Json.Nodes;

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
                    $"Active module {path.Value} statement identity changed; append Revoke before rerunning ledger-sync.");
            }

            if (active.FrozenNodeId != candidate.FrozenNodeId)
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} changed identity; run ledger-sync to reconcile it.");
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
            entry.LastAttestationEventHash)
        {
            AxiomClosure = entry.Payload.AxiomClosure,
        };
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
        return Append(baseline, ReattestationEvents(baseline, candidateCatalog));
    }

    public static ImmutableArray<byte> AppendSynchronization(
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog candidateCatalog)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidateCatalog);
        var reattestations = ReattestationEvents(baseline, candidateCatalog);
        var activeAfterReattestation = baseline.ActiveEntries.Values.ToDictionary(
            static entry => entry.Material.RepoPath,
            static entry => entry.Material);
        foreach (var (path, candidate) in candidateCatalog.ByPath)
        {
            if (activeAfterReattestation.ContainsKey(path))
            {
                activeAfterReattestation[path] = candidate;
            }
        }

        var freezes = MissingFreezeEvents(activeAfterReattestation, candidateCatalog);
        return Append(baseline, reattestations.AddRange(freezes));
    }

    private static ImmutableArray<(string Type, JsonElement Payload)> ReattestationEvents(
        FrozenLedgerConsistent baseline,
        FrozenMaterialCatalog candidateCatalog)
    {
        var activeByPath = baseline.ActiveEntries.Values.ToDictionary(
            static entry => entry.Material.RepoPath);
        var currentClosedPaths = candidateCatalog.Dag.Nodes
            .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
            .Select(static node => node.RepoPath)
            .ToHashSet();
        var payloads = ImmutableArray.CreateBuilder<(string Type, JsonElement Payload)>();
        foreach (var (path, entry) in activeByPath.OrderBy(
            static item => item.Key.Value,
            StringComparer.Ordinal))
        {
            if (!currentClosedPaths.Contains(path))
            {
                throw new InvalidOperationException(
                    $"Active module {path.Value} is no longer Closed; append Revoke before rerunning ledger-sync.");
            }

            if (!candidateCatalog.ByPath.TryGetValue(path, out var candidate))
            {
                continue;
            }

            if (entry.Payload.StatementId != candidate.StatementId
                || !entry.Payload.DeclarationStatementIds.SequenceEqual(candidate.DeclarationStatementIds))
            {
                var candidateInput = FrozenLedgerCanonicalWriter.FreezePayload(
                    candidateCatalog.Environment,
                    candidate).Input;
                var sourceUnchanged = entry.Payload.Input.DescriptorBlobOid
                    == candidateInput.DescriptorBlobOid;
                var pinsChanged = !entry.Payload.Input.SupportingBlobOids
                    .Order(StringComparer.Ordinal)
                    .SequenceEqual(
                        candidateInput.SupportingBlobOids.Order(StringComparer.Ordinal),
                        StringComparer.Ordinal);
                if (sourceUnchanged && pinsChanged)
                {
                    throw new InvalidOperationException(
                        $"Active module {path.Value} statement identity changed while its source blob is unchanged; run ledger-supersede for the environment-pin drift.");
                }

                throw new InvalidOperationException(
                    $"Active module {path.Value} statement identity changed without an admissible source-preserving environment-pin drift; append Revoke, then add a new Freeze before rerunning ledger-sync.");
            }

            var materialUnchanged = entry.Material.FrozenNodeId == candidate.FrozenNodeId
                && entry.Payload.Input.DescriptorBlobOid == candidate.Attestation.SourceBlobOid;
            if (materialUnchanged && entry.AxiomClosureKnown)
            {
                continue;
            }

            var input = FrozenLedgerCanonicalWriter.FreezePayload(
                candidateCatalog.Environment,
                candidate).Input;
            var payload = materialUnchanged
                ? new FrozenReattestPayload(
                    entry.Payload.CaseId,
                    input,
                    entry.LastAttestationEventHash)
                {
                    AxiomClosure = candidate.AxiomClosure,
                }
                : ExtendedReattestPayload(entry.Payload.CaseId, entry, candidate, input);
            payloads.Add(("Reattest", FrozenLedgerCanonicalWriter.ReattestElement(payload)));
        }

        return payloads.ToImmutable();
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
            material.PrerequisiteFrozenNodeIds,
            entry.LastAttestationEventHash,
            material.StatementId,
            material.WitnessId)
        {
            AxiomClosure = material.AxiomClosure,
        };

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
    internal const int CurrentDagSchemaVersion = 4;

    private sealed record EnvelopeField(string Name, bool InV1, bool InV2);

    private static readonly EnvelopeField[] EnvelopeFieldTable =
    {
        new("event_hash", InV1: true, InV2: true),
        new("event_type", InV1: true, InV2: true),
        new("payload", InV1: true, InV2: true),
        new("previous_hash", InV1: true, InV2: false),
        new("schema_version", InV1: true, InV2: true),
        new("sequence", InV1: true, InV2: false),
    };

    private static readonly string[] V1EnvelopeFields = EnvelopeFieldTable
        .Where(static field => field.InV1).Select(static field => field.Name).ToArray();

    private static readonly string[] V2EnvelopeFields = EnvelopeFieldTable
        .Where(static field => field.InV2).Select(static field => field.Name).ToArray();

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
                "repository-snapshot-v1",
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
            var element = JsonSerializer.SerializeToElement(new
            {
                case_id = payload.CaseId,
                input = InputElement(payload.Input),
                previous_attestation_event_hash = payload.PreviousAttestationEventHash,
            });
            return WithAxiomClosure(element, payload.AxiomClosure);
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
        var extended = JsonSerializer.SerializeToElement(new
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
            prerequisite_frozen_node_ids = payload.PrerequisiteFrozenNodeIds.Select(static id => id.Value),
            previous_attestation_event_hash = payload.PreviousAttestationEventHash,
            statement_id = statementId.Value,
            witness_id = witnessId.Value,
        });
        return WithAxiomClosure(extended, payload.AxiomClosure);
    }

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

    internal static JsonElement SupersedeElement(FrozenSupersedePayload payload)
    {
        var element = JsonSerializer.SerializeToElement(new
        {
            axiom_closure = payload.AxiomClosure,
            case_id = payload.CaseId,
            declaration_statement_ids = DeclarationStatementIdsElement(payload.DeclarationStatementIds),
            environment = EnvironmentPinsElement(payload.Environment),
            frozen_node_id = payload.FrozenNodeId.Value,
            input = InputElement(payload.Input),
            prerequisite_frozen_node_ids = payload.PrerequisiteFrozenNodeIds
                .Select(static id => id.Value),
            previous_attestation_event_hash = payload.PreviousAttestationEventHash,
            statement_id = payload.StatementId.Value,
            witness_id = payload.WitnessId.Value,
        });
        var result = JsonNode.Parse(element.GetRawText())!.AsObject();
        result["input"]!.AsObject().Remove("supporting_blob_oids");
        return JsonSerializer.SerializeToElement(result);
    }

    private static object DeclarationStatementIdsElement(
        ImmutableArray<FrozenDeclarationStatement> declarations) =>
        declarations.Select(static declaration => new
        {
            declaration_name_key = declaration.DeclarationNameKey,
            kind = declaration.Kind,
            statement_id = declaration.StatementId.Value,
        });

    internal static object EnvironmentPinsElement(FrozenEnvironmentPins environment) => new
    {
        lake_manifest_blob_oid = environment.LakeManifestBlobOid,
        lakefile_blob_oid = environment.LakefileBlobOid,
        lakefile_path = environment.LakefilePath.Value,
        lean_toolchain_blob_oid = environment.LeanToolchainBlobOid,
    };

    internal static JsonElement EnvironmentReferenceElement(FrozenEnvironmentReference reference) =>
        JsonSerializer.SerializeToElement(new
        {
            environment = EnvironmentPinsElement(reference.Environment),
            input = InputElement(reference.Input),
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
        WriteEnvelope(eventType, payload, 1, previousHash, sequence);

    internal static (ImmutableArray<byte> Bytes, string Hash) WriteDagEvent(
        string eventType,
        JsonElement payload,
        int schemaVersion = CurrentDagSchemaVersion)
    {
        if (schemaVersion is not (2 or 3 or CurrentDagSchemaVersion))
        {
            throw new ArgumentOutOfRangeException(
                nameof(schemaVersion),
                "Content-addressed event schema_version must be 2, 3, or 4.");
        }

        return WriteEnvelope(eventType, payload, schemaVersion, null, null);
    }

    internal static bool ValidateDagEvent(
        JsonElement value,
        out string identity,
        out string eventHash,
        out string message)
    {
        identity = string.Empty;
        eventHash = string.Empty;
        message = string.Empty;
        if (value.ValueKind != JsonValueKind.Object
            || !HasExactFields(value, V2EnvelopeFields))
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

        if (version is not (2 or 3 or CurrentDagSchemaVersion))
        {
            message = "content-addressed event schema_version must be 2, 3, or 4.";
            return false;
        }

        var encoded = WriteDagEvent(eventType.GetString()!, payload, version);
        eventHash = claimedHash.GetString()!;
        if (!string.Equals(encoded.Hash, eventHash, StringComparison.Ordinal))
        {
            message = "event_hash does not match canonical content.";
            return false;
        }

        identity = EventIdentity(eventType.GetString()!, payload, eventHash, version);
        return true;
    }

    internal static string EventIdentity(string eventType, JsonElement payload, string eventHash) =>
        EventIdentity(eventType, payload, eventHash, CurrentDagSchemaVersion);

    internal static string EventIdentity(
        string eventType,
        JsonElement payload,
        string eventHash,
        int schemaVersion)
    {
        if (schemaVersion >= 4 || eventType == FrozenLedger.SupersedeEventType)
        {
            return eventHash;
        }

        return payload.TryGetProperty("frozen_node_id", out var frozenNodeId)
            && frozenNodeId.ValueKind == JsonValueKind.String
            ? frozenNodeId.GetString()!
            : eventHash;
    }

    private static (ImmutableArray<byte> Bytes, string Hash) WriteEnvelope(
        string eventType,
        JsonElement payload,
        int schemaVersion,
        string? previousHash,
        int? sequence)
    {
        var withoutHash = Envelope(eventType, payload, schemaVersion, previousHash, sequence, null);
        var hash = FrozenContentHash.Compute(
            FrozenHashDomains.FrozenEvent,
            StructuredCanonicalWriter.WriteJson(withoutHash).AsSpan());
        var complete = Envelope(eventType, payload, schemaVersion, previousHash, sequence, hash);
        return (StructuredCanonicalWriter.WriteJson(complete), hash);
    }

    private static JsonElement Envelope(
        string eventType,
        JsonElement payload,
        int schemaVersion,
        string? previousHash,
        int? sequence,
        string? eventHash)
    {
        var fields = schemaVersion == 1 ? V1EnvelopeFields : V2EnvelopeFields;
        var envelope = new JsonObject();
        foreach (var field in fields)
        {
            JsonNode? value = field switch
            {
                "event_hash" => eventHash,
                "event_type" => eventType,
                "payload" => JsonNode.Parse(payload.GetRawText()),
                "previous_hash" => previousHash,
                "schema_version" => schemaVersion,
                "sequence" => sequence,
                _ => throw new InvalidOperationException("unknown frozen ledger envelope field"),
            };
            if (value is not null)
            {
                envelope.Add(field, value);
            }
        }

        return JsonSerializer.SerializeToElement(envelope);
    }

    private static bool HasExactFields(JsonElement value, IEnumerable<string> expected)
    {
        var actual = value.EnumerateObject().Select(static property => property.Name).ToArray();
        return actual.Length == actual.Distinct(StringComparer.Ordinal).Count()
            && actual.Order(StringComparer.Ordinal).SequenceEqual(expected.Order(StringComparer.Ordinal));
    }
}
