using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    internal const string SupersedeEventType = "Supersede";

    internal static FrozenSupersedePayload ParseSupersede(JsonElement payload)
    {
        RequireObjectFields(
            payload,
            "Supersede payload",
            FrozenLedgerReferenceProjection.SupersedePayloadFields);
        var result = new FrozenSupersedePayload(
            ParseSortedUniqueStrings(payload, "axiom_closure"),
            RequiredString(payload, "case_id"),
            ParseDeclarationStatementArray(payload.GetProperty("declaration_statement_ids")),
            ParseEnvironmentPins(payload.GetProperty("environment")),
            ParseFrozenNodeId(RequiredString(payload, "frozen_node_id"), "Supersede frozen node"),
            ParseSupersedeInput(payload.GetProperty("input")),
            ParseFrozenNodeIds(payload, "prerequisite_frozen_node_ids"),
            RequiredString(payload, "previous_attestation_event_hash"),
            ParseStatementId(RequiredString(payload, "statement_id"), "Supersede statement"),
            ParseWitnessId(RequiredString(payload, "witness_id"), "Supersede witness"));
        ValidateSupersedeSyntax(result);
        return result;
    }

    internal static FrozenSupersedePayload ValidateSupersede(
        JsonElement payload,
        IReadOnlyDictionary<string, FrozenActiveEntry> active,
        TrustedFrozenGitReferences trustedReferences,
        FrozenMaterialCatalog? candidateCatalog,
        bool repositoryImportClosureUnchanged)
    {
        var result = ParseSupersede(payload);
        if (!active.TryGetValue(result.CaseId, out var entry)
            || result.PreviousAttestationEventHash != entry.LastAttestationEventHash)
        {
            throw new FormatException(
                "Supersede targets no active case or does not extend its attestation chain.");
        }

        ValidateSupersedeStrength(result, entry, repositoryImportClosureUnchanged);

        var reference = new FrozenEnvironmentReference(result.Input, result.Environment);
        if (!trustedReferences.Covers(result.Input) || !trustedReferences.Covers(reference))
        {
            throw new FormatException(
                "Supersede fresh input or named environment pins lack validated Git capabilities.");
        }

        if (candidateCatalog is not null)
        {
            ValidateSupersedeCandidateState(result, entry.Material.RepoPath, candidateCatalog);
        }

        return result;
    }

    internal static void ValidateSupersedeStrength(
        FrozenSupersedePayload payload,
        FrozenActiveEntry protectedBaseEntry,
        bool repositoryImportClosureUnchanged)
    {
        if (!protectedBaseEntry.AxiomClosureKnown)
        {
            throw new FormatException(
                $"Supersede target {protectedBaseEntry.Material.RepoPath.Value} recorded axiom closure is unknown.");
        }

        var declarationKeys = payload.DeclarationStatementIds
            .Select(static declaration => (declaration.Kind, declaration.DeclarationNameKey))
            .OrderBy(static declaration => declaration.Kind, StringComparer.Ordinal)
            .ThenBy(static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal);
        var protectedDeclarationKeys = protectedBaseEntry.Payload.DeclarationStatementIds
            .Select(static declaration => (declaration.Kind, declaration.DeclarationNameKey))
            .OrderBy(static declaration => declaration.Kind, StringComparer.Ordinal)
            .ThenBy(static declaration => declaration.DeclarationNameKey, StringComparer.Ordinal);
        if (!declarationKeys.SequenceEqual(protectedDeclarationKeys))
        {
            throw new FormatException(
                $"Supersede target {protectedBaseEntry.Material.RepoPath.Value} declaration keys differ from the protected-base node.");
        }

        if (payload.StatementId != protectedBaseEntry.Material.StatementId)
        {
            if (!EnvironmentPinsChanged(payload.Environment, protectedBaseEntry))
            {
                throw new FormatException(
                    $"Supersede target {protectedBaseEntry.Material.RepoPath.Value} statement identity changed but environment pins did not change.");
            }

            // Branch B attributes drift to the environment only when both the descriptor and its
            // transitive repository import closure are unchanged.
            if (payload.Input.DescriptorBlobOid
                != protectedBaseEntry.Payload.Input.DescriptorBlobOid)
            {
                throw new FormatException(
                    $"Supersede target {protectedBaseEntry.Material.RepoPath.Value} statement identity and source blob both changed from the protected-base node.");
            }

            if (!repositoryImportClosureUnchanged)
            {
                throw new FormatException(
                    $"Supersede target {protectedBaseEntry.Material.RepoPath.Value} statement identity changed while its repository import closure changed from the protected base.");
            }
        }

        if (payload.AxiomClosure.Except(
                protectedBaseEntry.Material.AxiomClosure,
                StringComparer.Ordinal).Any())
        {
            throw new FormatException(
                $"Supersede target {protectedBaseEntry.Material.RepoPath.Value} axiom closure is not a subset of the protected-base closure.");
        }
    }

    internal static bool EnvironmentPinsChanged(
        FrozenEnvironmentPins candidate,
        FrozenActiveEntry protectedBaseEntry)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(protectedBaseEntry);
        if (protectedBaseEntry.Environment is { } protectedEnvironment)
        {
            return candidate != protectedEnvironment;
        }

        return LegacyEnvironmentPinsChanged(
            candidate.LakeManifestBlobOid,
            candidate.LeanToolchainBlobOid,
            protectedBaseEntry);
    }

    internal static bool EnvironmentPinsChanged(
        FrozenEnvironmentAttestation candidate,
        FrozenActiveEntry protectedBaseEntry)
    {
        ArgumentNullException.ThrowIfNull(candidate);
        ArgumentNullException.ThrowIfNull(protectedBaseEntry);
        if (protectedBaseEntry.Environment is { } protectedEnvironment)
        {
            if (candidate.LakefilePath is null
                || candidate.LakefileBlobOid is null
                || !RepoPath.TryCreate(candidate.LakefilePath, out var lakefilePath))
            {
                return true;
            }

            return new FrozenEnvironmentPins(
                candidate.LakeManifestBlobOid,
                candidate.LakefileBlobOid,
                lakefilePath,
                candidate.LeanToolchainBlobOid) != protectedEnvironment;
        }

        return LegacyEnvironmentPinsChanged(
            candidate.LakeManifestBlobOid,
            candidate.LeanToolchainBlobOid,
            protectedBaseEntry);
    }

    private static bool LegacyEnvironmentPinsChanged(
        string lakeManifestBlobOid,
        string leanToolchainBlobOid,
        FrozenActiveEntry protectedBaseEntry)
    {
        var candidateLegacyPins = new[]
        {
            lakeManifestBlobOid,
            leanToolchainBlobOid,
        }.Order(StringComparer.Ordinal);
        return !candidateLegacyPins.SequenceEqual(
            protectedBaseEntry.Payload.Input.SupportingBlobOids.Order(StringComparer.Ordinal),
            StringComparer.Ordinal);
    }

    internal static FrozenActiveEntry ApplySupersede(
        FrozenActiveEntry entry,
        FrozenSupersedePayload payload,
        string eventHash,
        FrozenNodeMaterial? validatedMaterial = null)
    {
        var path = entry.Material.RepoPath;
        var material = validatedMaterial ?? new FrozenNodeMaterial(
            path,
            payload.DeclarationStatementIds,
            payload.StatementId,
            payload.WitnessId,
            payload.FrozenNodeId,
            payload.PrerequisiteFrozenNodeIds,
            payload.AxiomClosure,
            new FrozenModuleAttestation(path, payload.Input.DescriptorBlobOid)
            {
                BaseCommitOid = payload.Input.BaseCommitOid,
                BaseTreeOid = payload.Input.BaseTreeOid,
            });
        return entry with
        {
            Material = material,
            Payload = entry.Payload with
            {
                AxiomClosure = payload.AxiomClosure,
                DeclarationStatementIds = payload.DeclarationStatementIds,
                FrozenNodeId = payload.FrozenNodeId,
                Input = payload.Input,
                PrerequisiteFrozenNodeIds = payload.PrerequisiteFrozenNodeIds,
                StatementId = payload.StatementId,
                WitnessId = payload.WitnessId,
            },
            LastAttestationEventHash = eventHash,
            AxiomClosureKnown = true,
            Environment = payload.Environment,
        };
    }

    internal static FrozenEnvironmentPins EnvironmentPins(FrozenEnvironmentAttestation environment)
    {
        ArgumentNullException.ThrowIfNull(environment);
        if (environment.LakefilePath is null
            || environment.LakefileBlobOid is null
            || !RepoPath.TryCreate(environment.LakefilePath, out var lakefilePath))
        {
            throw new InvalidOperationException(
                "Supersede requires a candidate environment with a named lakefile pin.");
        }

        return new FrozenEnvironmentPins(
            environment.LakeManifestBlobOid,
            environment.LakefileBlobOid,
            lakefilePath,
            environment.LeanToolchainBlobOid);
    }

    private static void ValidateSupersedeCandidateState(
        FrozenSupersedePayload payload,
        RepoPath path,
        FrozenMaterialCatalog candidateCatalog)
    {
        if (!candidateCatalog.ByPath.TryGetValue(path, out var candidate))
        {
            throw new FormatException($"Supersede target {path.Value} is not Closed.");
        }

        var environment = candidateCatalog.Environment;
        if (payload.Input.DescriptorSelector != path.Value
            || !payload.DeclarationStatementIds.SequenceEqual(candidate.DeclarationStatementIds)
            || payload.StatementId != candidate.StatementId
            || payload.WitnessId != candidate.WitnessId
            || payload.FrozenNodeId != candidate.FrozenNodeId
            || !payload.PrerequisiteFrozenNodeIds.SequenceEqual(candidate.PrerequisiteFrozenNodeIds)
            || !payload.AxiomClosure.SequenceEqual(candidate.AxiomClosure)
            || payload.Input.DescriptorBlobOid != candidate.Attestation.SourceBlobOid
            || payload.Input.BaseCommitOid
                != (candidate.Attestation.BaseCommitOid ?? environment.OriginCommitOid)
            || payload.Input.BaseTreeOid
                != (candidate.Attestation.BaseTreeOid ?? environment.OriginTreeOid)
            || payload.Environment != EnvironmentPins(environment))
        {
            throw new FormatException(
                $"Supersede fresh coordinates do not match candidate Closed material for {path.Value}.");
        }
    }

    private static FrozenEnvironmentPins ParseEnvironmentPins(JsonElement value)
    {
        RequireObjectFields(
            value,
            "Supersede environment",
            "lake_manifest_blob_oid", "lakefile_blob_oid", "lakefile_path",
            "lean_toolchain_blob_oid");
        var lakefilePath = RequiredString(value, "lakefile_path");
        if (!RepoPath.TryCreate(lakefilePath, out var parsedPath)
            || parsedPath.Value is not ("lakefile.toml" or "lakefile.lean"))
        {
            throw new FormatException(
                "Supersede lakefile_path must be lakefile.toml or lakefile.lean.");
        }

        var result = new FrozenEnvironmentPins(
            RequiredString(value, "lake_manifest_blob_oid"),
            RequiredString(value, "lakefile_blob_oid"),
            parsedPath,
            RequiredString(value, "lean_toolchain_blob_oid"));
        if (EnvironmentPinOids(result).Any(static oid => !FrozenHashSyntax.IsGitOid(oid)))
        {
            throw new FormatException("Supersede environment has a malformed Git blob OID.");
        }

        return result;
    }

    private static FrozenLedgerInput ParseSupersedeInput(JsonElement value)
    {
        RequireObjectFields(
            value,
            "Supersede input",
            "base_commit_oid", "base_tree_oid", "descriptor_blob_oid", "descriptor_selector",
            "materializer");
        var result = new FrozenLedgerInput(
            RequiredString(value, "base_commit_oid"),
            RequiredString(value, "base_tree_oid"),
            RequiredString(value, "descriptor_blob_oid"),
            RequiredString(value, "descriptor_selector"),
            RequiredString(value, "materializer"),
            ImmutableArray<string>.Empty);
        if (!FrozenHashSyntax.IsGitOid(result.BaseCommitOid)
            || !FrozenHashSyntax.IsGitOid(result.BaseTreeOid)
            || !FrozenHashSyntax.IsGitOid(result.DescriptorBlobOid))
        {
            throw new FormatException("Supersede input has a malformed Git object reference.");
        }

        return result;
    }

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

    private static ImmutableArray<string> ParseAxiomClosure(JsonElement payload, string name) =>
        ParseSortedUniqueStrings(payload, name);

    private static void ValidateSupersedeSyntax(FrozenSupersedePayload payload)
    {
        if (!FrozenHashSyntax.IsSha256(payload.PreviousAttestationEventHash))
        {
            throw new FormatException("Supersede previous_attestation_event_hash is malformed.");
        }

        if (payload.Input.DescriptorSelector.Length == 0
            || payload.Input.Materializer != "repository-snapshot-v1")
        {
            throw new FormatException(
                "Supersede input must select a source using repository-snapshot-v1.");
        }

        var path = RepoPath.CreateKnown(payload.Input.DescriptorSelector);
        var statement = StatementId.Create(FrozenContentHash.Compute(
            FrozenHashDomains.Statement,
            CanonicalStatementWriter.WriteModule(
                path,
                payload.DeclarationStatementIds).AsSpan()));
        if (payload.StatementId != statement)
        {
            throw new FormatException(
                "Supersede statement ID does not match declaration statement IDs.");
        }

        if (!payload.Input.SupportingBlobOids.IsEmpty)
        {
            throw new FormatException(
                "Supersede input must not duplicate its named environment pins.");
        }
    }

    private static IEnumerable<string> EnvironmentPinOids(FrozenEnvironmentPins environment)
    {
        yield return environment.LakeManifestBlobOid;
        yield return environment.LakefileBlobOid;
        yield return environment.LeanToolchainBlobOid;
    }
}
