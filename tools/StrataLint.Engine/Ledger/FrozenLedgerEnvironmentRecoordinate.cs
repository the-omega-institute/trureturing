using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    internal const string EnvironmentRecoordinateEventType = "EnvironmentRecoordinate";
    internal const string EnvironmentRecoordinateUnprovedEquivalence =
        "representation-migration; equivalence-unproved";

    internal static FrozenEnvironmentRecoordinatePayload ParseEnvironmentRecoordinate(
        JsonElement payload)
    {
        RequireObjectFields(
            payload,
            "EnvironmentRecoordinate payload",
            "case_id", "declaration_statement_ids", "environment", "equivalence_status",
            "kernel_verdict", "new_axiom_closure", "new_frozen_node_id", "new_input",
            "new_imports", "new_prerequisite_frozen_node_ids", "new_statement_id", "new_witness_id",
            "old_axiom_closure", "old_frozen_node_id", "old_imports", "old_input",
            "old_prerequisite_frozen_node_ids", "old_statement_id", "old_witness_id",
            "previous_attestation_event_hash", "source_sha256");
        var declarations = payload.GetProperty("declaration_statement_ids");
        RequireObjectFields(declarations, "EnvironmentRecoordinate declarations", "new", "old");
        var environments = payload.GetProperty("environment");
        RequireObjectFields(environments, "EnvironmentRecoordinate environment", "new", "old");
        var result = new FrozenEnvironmentRecoordinatePayload(
            RequiredString(payload, "case_id"),
            ParseDeclarationStatementArray(declarations.GetProperty("new")),
            ParseDeclarationStatementArray(declarations.GetProperty("old")),
            ParseEnvironmentPins(environments.GetProperty("new"), "new"),
            ParseEnvironmentPins(environments.GetProperty("old"), "old"),
            RequiredString(payload, "equivalence_status"),
            RequiredString(payload, "kernel_verdict"),
            ParseAxiomClosure(payload, "new_axiom_closure"),
            ParseFrozenNodeId(RequiredString(payload, "new_frozen_node_id"), "new frozen node"),
            ParseSortedUniqueStrings(payload, "new_imports"),
            ParseInput(payload.GetProperty("new_input")),
            ParseFrozenNodeIds(payload, "new_prerequisite_frozen_node_ids"),
            ParseStatementId(RequiredString(payload, "new_statement_id"), "new statement"),
            ParseWitnessId(RequiredString(payload, "new_witness_id"), "new witness"),
            ParseAxiomClosure(payload, "old_axiom_closure"),
            ParseFrozenNodeId(RequiredString(payload, "old_frozen_node_id"), "old frozen node"),
            ParseSortedUniqueStrings(payload, "old_imports"),
            ParseInput(payload.GetProperty("old_input")),
            ParseFrozenNodeIds(payload, "old_prerequisite_frozen_node_ids"),
            ParseStatementId(RequiredString(payload, "old_statement_id"), "old statement"),
            ParseWitnessId(RequiredString(payload, "old_witness_id"), "old witness"),
            RequiredString(payload, "previous_attestation_event_hash"),
            RequiredString(payload, "source_sha256"));
        ValidateEnvironmentRecoordinateSyntax(result);
        return result;
    }

    private static FrozenEnvironmentRecoordinatePayload ValidateEnvironmentRecoordinate(
        JsonElement payload,
        IReadOnlyDictionary<string, FrozenActiveEntry> active,
        TrustedFrozenGitReferences trustedReferences,
        FrozenMaterialCatalog? candidateCatalog)
    {
        var result = ParseEnvironmentRecoordinate(payload);
        if (!active.TryGetValue(result.CaseId, out var entry)
            || result.PreviousAttestationEventHash != entry.LastAttestationEventHash)
        {
            throw new FormatException(
                "EnvironmentRecoordinate targets no active case or does not extend its attestation chain.");
        }

        if (!trustedReferences.Covers(result.OldInput)
            || !trustedReferences.Covers(result.NewInput)
            || !trustedReferences.Covers(new FrozenEnvironmentReference(
                result.OldInput,
                result.OldEnvironment,
                result.SourceSha256))
            || !trustedReferences.Covers(new FrozenEnvironmentReference(
                result.NewInput,
                result.NewEnvironment,
                result.SourceSha256)))
        {
            throw new FormatException(
                "EnvironmentRecoordinate inputs or named environment pins lack validated Git capabilities.");
        }

        ValidateOldActiveState(result, entry);
        if (candidateCatalog is not null)
        {
            if (!candidateCatalog.ByPath.TryGetValue(entry.Material.RepoPath, out var candidate))
            {
                throw new FormatException(
                    $"EnvironmentRecoordinate target {entry.Material.RepoPath.Value} is not Closed.");
            }

            ValidateNewCandidateState(result, candidate, candidateCatalog.Environment);
        }

        return result;
    }

    private static void ValidateOldActiveState(
        FrozenEnvironmentRecoordinatePayload payload,
        FrozenActiveEntry entry)
    {
        var material = entry.Material;
        var oldLegacyPins = new[]
        {
            payload.OldEnvironment.LakeManifestBlobOid,
            payload.OldEnvironment.LeanToolchainBlobOid,
        }.Order(StringComparer.Ordinal);
        var oldCompletePins = EnvironmentPinOids(payload.OldEnvironment).Order(StringComparer.Ordinal);
        var priorPinsMatch = entry.Payload.Input.SupportingBlobOids.SequenceEqual(
                oldLegacyPins,
                StringComparer.Ordinal)
            || entry.Payload.Input.SupportingBlobOids.SequenceEqual(
                oldCompletePins,
                StringComparer.Ordinal);
        if (payload.OldInput.DescriptorSelector != material.RepoPath.Value
            || payload.OldDeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds) is false
            || payload.OldStatementId != material.StatementId
            || payload.OldWitnessId != material.WitnessId
            || payload.OldFrozenNodeId != material.FrozenNodeId
            || !payload.OldPrerequisiteFrozenNodeIds.SequenceEqual(material.PrerequisiteFrozenNodeIds)
            || payload.OldInput.DescriptorBlobOid != material.Attestation.SourceBlobOid
            || payload.OldInput.BaseCommitOid != entry.Payload.Input.BaseCommitOid
            || payload.OldInput.BaseTreeOid != entry.Payload.Input.BaseTreeOid
            || payload.OldInput.Materializer != entry.Payload.Input.Materializer
            || !priorPinsMatch
            || entry.Environment is not null
                && entry.Environment != payload.OldEnvironment
            || entry.AxiomClosureKnown
                && !payload.OldAxiomClosure.SequenceEqual(material.AxiomClosure))
        {
            throw new FormatException(
                "EnvironmentRecoordinate old coordinates do not match the active Freeze/attestation state.");
        }
    }

    private static void ValidateNewCandidateState(
        FrozenEnvironmentRecoordinatePayload payload,
        FrozenNodeMaterial material,
        FrozenEnvironmentAttestation environment)
    {
        if (payload.NewInput.DescriptorSelector != material.RepoPath.Value
            || !payload.NewDeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds)
            || payload.NewStatementId != material.StatementId
            || payload.NewWitnessId != material.WitnessId
            || payload.NewFrozenNodeId != material.FrozenNodeId
            || !payload.NewPrerequisiteFrozenNodeIds.SequenceEqual(material.PrerequisiteFrozenNodeIds)
            || !payload.NewAxiomClosure.SequenceEqual(material.AxiomClosure)
            || payload.NewInput.DescriptorBlobOid != material.Attestation.SourceBlobOid
            || payload.NewInput.BaseCommitOid
                != (material.Attestation.BaseCommitOid ?? environment.OriginCommitOid)
            || payload.NewInput.BaseTreeOid
                != (material.Attestation.BaseTreeOid ?? environment.OriginTreeOid)
            || payload.NewEnvironment.LeanToolchainBlobOid != environment.LeanToolchainBlobOid
            || payload.NewEnvironment.LakeManifestBlobOid != environment.LakeManifestBlobOid
            || payload.NewEnvironment.LakefilePath.Value != environment.LakefilePath
            || payload.NewEnvironment.LakefileBlobOid != environment.LakefileBlobOid)
        {
            throw new FormatException(
                $"EnvironmentRecoordinate new coordinates do not match candidate Closed material for {material.RepoPath.Value}.");
        }
    }

    private static FrozenActiveEntry ApplyEnvironmentRecoordinate(
        FrozenActiveEntry entry,
        FrozenEnvironmentRecoordinatePayload payload,
        string eventHash)
    {
        var path = entry.Material.RepoPath;
        var material = new FrozenNodeMaterial(
            path,
            payload.NewDeclarationStatementIds,
            payload.NewStatementId,
            payload.NewWitnessId,
            payload.NewFrozenNodeId,
            payload.NewPrerequisiteFrozenNodeIds,
            payload.NewAxiomClosure,
            new FrozenModuleAttestation(path, payload.NewInput.DescriptorBlobOid)
            {
                BaseCommitOid = payload.NewInput.BaseCommitOid,
                BaseTreeOid = payload.NewInput.BaseTreeOid,
            });
        return entry with
        {
            Material = material,
            Payload = entry.Payload with
            {
                DeclarationStatementIds = payload.NewDeclarationStatementIds,
                FrozenNodeId = payload.NewFrozenNodeId,
                Input = payload.NewInput,
                InputFingerprint = payload.NewWitnessId.Value,
                PrerequisiteFrozenNodeIds = payload.NewPrerequisiteFrozenNodeIds,
                SemanticReceipt = payload.NewFrozenNodeId.Value,
                StatementId = payload.NewStatementId,
                WitnessId = payload.NewWitnessId,
            },
            LastAttestationEventHash = eventHash,
            AxiomClosureKnown = true,
            Environment = payload.NewEnvironment,
        };
    }

    private static FrozenEnvironmentPins ParseEnvironmentPins(JsonElement value, string side)
    {
        RequireObjectFields(
            value,
            $"EnvironmentRecoordinate {side} environment",
            "lake_manifest_blob_oid", "lakefile_blob_oid", "lakefile_path",
            "lean_toolchain_blob_oid");
        var lakefilePath = RequiredString(value, "lakefile_path");
        if (!RepoPath.TryCreate(lakefilePath, out var parsedPath)
            || parsedPath.Value is not ("lakefile.toml" or "lakefile.lean"))
        {
            throw new FormatException(
                $"EnvironmentRecoordinate {side} lakefile_path must be lakefile.toml or lakefile.lean.");
        }

        var result = new FrozenEnvironmentPins(
            RequiredString(value, "lake_manifest_blob_oid"),
            RequiredString(value, "lakefile_blob_oid"),
            parsedPath,
            RequiredString(value, "lean_toolchain_blob_oid"));
        if (EnvironmentPinOids(result).Any(static oid => !FrozenHashSyntax.IsGitOid(oid)))
        {
            throw new FormatException(
                $"EnvironmentRecoordinate {side} environment has a malformed Git blob OID.");
        }

        return result;
    }

    private static ImmutableArray<string> ParseAxiomClosure(JsonElement payload, string name) =>
        ParseSortedUniqueStrings(payload, name);

    private static ImmutableArray<string> ParseSortedUniqueStrings(JsonElement payload, string name)
    {
        var result = RequiredStringArray(payload, name);
        if (!result.SequenceEqual(result.Order(StringComparer.Ordinal), StringComparer.Ordinal)
            || result.Distinct(StringComparer.Ordinal).Count() != result.Length)
        {
            throw new FormatException($"{name} must be unique and in canonical ordinal order.");
        }

        return result;
    }

    private static void ValidateEnvironmentRecoordinateSyntax(
        FrozenEnvironmentRecoordinatePayload payload)
    {
        if (!FrozenHashSyntax.IsSha256(payload.PreviousAttestationEventHash))
        {
            throw new FormatException(
                "EnvironmentRecoordinate previous_attestation_event_hash is malformed.");
        }

        if (!FrozenHashSyntax.IsSha256(payload.SourceSha256))
        {
            throw new FormatException("EnvironmentRecoordinate source_sha256 is malformed.");
        }

        if (payload.EquivalenceStatus != EnvironmentRecoordinateUnprovedEquivalence)
        {
            throw new FormatException(
                "EnvironmentRecoordinate v1 only accepts representation-migration; equivalence-unproved.");
        }

        if (payload.KernelVerdict != nameof(TruthState.Closed))
        {
            throw new FormatException("EnvironmentRecoordinate kernel_verdict must be Closed.");
        }

        if (payload.OldEnvironment == payload.NewEnvironment)
        {
            throw new FormatException(
                "EnvironmentRecoordinate requires distinct old and new environments; unchanged environment uses Reattest.");
        }

        var path = RepoPath.CreateKnown(payload.OldInput.DescriptorSelector);
        var oldModuleStatement = StatementId.Create(FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(
                path,
                payload.OldDeclarationStatementIds).AsSpan()));
        var newModuleStatement = StatementId.Create(FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(
                path,
                payload.NewDeclarationStatementIds).AsSpan()));
        if (payload.OldStatementId != oldModuleStatement
            || payload.NewStatementId != newModuleStatement)
        {
            throw new FormatException(
                "EnvironmentRecoordinate module statement IDs do not match declaration statement IDs.");
        }

        if (payload.OldInput.DescriptorBlobOid != payload.NewInput.DescriptorBlobOid)
        {
            throw new FormatException(
                "EnvironmentRecoordinate source blob OIDs must be byte-identical.");
        }

        if (payload.OldInput.DescriptorSelector != payload.NewInput.DescriptorSelector
            || payload.OldInput.Materializer != "repository-snapshot-v1"
            || payload.NewInput.Materializer != "repository-snapshot-v1")
        {
            throw new FormatException(
                "EnvironmentRecoordinate inputs must select the same source using repository-snapshot-v1.");
        }

        RequireInputPins(payload.OldInput, payload.OldEnvironment, "old");
        RequireInputPins(payload.NewInput, payload.NewEnvironment, "new");
        ValidateRecoordinateContentAddresses(payload);
        var oldKeys = DeclarationKeys(payload.OldDeclarationStatementIds);
        var newKeys = DeclarationKeys(payload.NewDeclarationStatementIds);
        if (!oldKeys.SequenceEqual(newKeys, StringComparer.Ordinal))
        {
            throw new FormatException(
                "EnvironmentRecoordinate declaration name and kind set changed.");
        }

        if (payload.NewAxiomClosure.Except(payload.OldAxiomClosure, StringComparer.Ordinal).Any())
        {
            throw new FormatException("EnvironmentRecoordinate axiom closure expanded.");
        }
    }

    private static void ValidateRecoordinateContentAddresses(
        FrozenEnvironmentRecoordinatePayload payload)
    {
        var path = RepoPath.CreateKnown(payload.OldInput.DescriptorSelector);
        var oldWitness = FrozenContentAddress.ComputeWitnessId(
            path,
            payload.OldStatementId,
            payload.OldImports,
            payload.OldAxiomClosure,
            payload.OldInput.DescriptorBlobOid,
            payload.SourceSha256,
            payload.OldEnvironment.LeanToolchainBlobOid,
            payload.OldEnvironment.LakeManifestBlobOid);
        var newWitness = FrozenContentAddress.ComputeWitnessId(
            path,
            payload.NewStatementId,
            payload.NewImports,
            payload.NewAxiomClosure,
            payload.NewInput.DescriptorBlobOid,
            payload.SourceSha256,
            payload.NewEnvironment.LeanToolchainBlobOid,
            payload.NewEnvironment.LakeManifestBlobOid);
        var oldFrozen = FrozenContentAddress.ComputeFrozenNodeId(
            path,
            payload.OldStatementId,
            oldWitness,
            payload.OldPrerequisiteFrozenNodeIds);
        var newFrozen = FrozenContentAddress.ComputeFrozenNodeId(
            path,
            payload.NewStatementId,
            newWitness,
            payload.NewPrerequisiteFrozenNodeIds);
        if (oldWitness != payload.OldWitnessId
            || newWitness != payload.NewWitnessId
            || oldFrozen != payload.OldFrozenNodeId
            || newFrozen != payload.NewFrozenNodeId)
        {
            throw new FormatException(
                "EnvironmentRecoordinate witness or frozen-node address does not match its evidence.");
        }
    }

    private static void RequireInputPins(
        FrozenLedgerInput input,
        FrozenEnvironmentPins environment,
        string side)
    {
        var expected = EnvironmentPinOids(environment).Order(StringComparer.Ordinal);
        if (!input.SupportingBlobOids.SequenceEqual(expected, StringComparer.Ordinal))
        {
            throw new FormatException(
                $"EnvironmentRecoordinate {side} input does not contain exactly its three environment pins.");
        }
    }

    private static IEnumerable<string> EnvironmentPinOids(FrozenEnvironmentPins environment)
    {
        yield return environment.LakeManifestBlobOid;
        yield return environment.LakefileBlobOid;
        yield return environment.LeanToolchainBlobOid;
    }

    private static IEnumerable<string> DeclarationKeys(
        ImmutableArray<FrozenDeclarationStatement> declarations) =>
        declarations.Select(static item => item.DeclarationNameKey + "\0" + item.Kind);
}
