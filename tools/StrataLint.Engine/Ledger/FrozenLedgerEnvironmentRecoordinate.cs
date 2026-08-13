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
            "new_prerequisite_frozen_node_ids", "new_statement_id", "new_witness_id",
            "old_axiom_closure", "old_frozen_node_id", "old_input",
            "old_prerequisite_frozen_node_ids", "old_statement_id", "old_witness_id",
            "previous_attestation_event_hash");
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
            ParseInput(payload.GetProperty("new_input")),
            ParseFrozenNodeIds(payload, "new_prerequisite_frozen_node_ids"),
            ParseStatementId(RequiredString(payload, "new_statement_id"), "new statement"),
            ParseWitnessId(RequiredString(payload, "new_witness_id"), "new witness"),
            ParseAxiomClosure(payload, "old_axiom_closure"),
            ParseFrozenNodeId(RequiredString(payload, "old_frozen_node_id"), "old frozen node"),
            ParseInput(payload.GetProperty("old_input")),
            ParseFrozenNodeIds(payload, "old_prerequisite_frozen_node_ids"),
            ParseStatementId(RequiredString(payload, "old_statement_id"), "old statement"),
            ParseWitnessId(RequiredString(payload, "old_witness_id"), "old witness"),
            RequiredString(payload, "previous_attestation_event_hash"));
        ValidateEnvironmentRecoordinateSyntax(result);
        return result;
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

    private static ImmutableArray<string> ParseAxiomClosure(JsonElement payload, string name)
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

        if (payload.EquivalenceStatus != EnvironmentRecoordinateUnprovedEquivalence)
        {
            throw new FormatException(
                "EnvironmentRecoordinate v1 only accepts representation-migration; equivalence-unproved.");
        }

        if (payload.KernelVerdict != nameof(TruthState.Closed))
        {
            throw new FormatException("EnvironmentRecoordinate kernel_verdict must be Closed.");
        }

        if (payload.OldStatementId == payload.NewStatementId)
        {
            throw new FormatException(
                "EnvironmentRecoordinate requires statement identity drift; unchanged identity uses Reattest.");
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
