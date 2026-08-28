using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    private static RevocationEvidence ParseEvidence(JsonElement value)
    {
        var type = RequiredString(value, "evidence_type");
        var root = ParseFrozenNodeId(RequiredString(value, "root_frozen_node_id"), "evidence root");
        return type switch
        {
            nameof(RevocationEvidence.KernelWitnessFailure) => ParseKernelWitnessFailure(value, root),
            nameof(RevocationEvidence.AllowedAxiomRetired) => ParseAllowedAxiomRetired(value, root),
            nameof(RevocationEvidence.FormalContradictionCertificate) =>
                ParseFormalContradiction(value, root),
            nameof(RevocationEvidence.ContentAddressMismatch) =>
                ParseContentAddressMismatch(value, root),
            _ => throw new FormatException($"Unknown revocation evidence type {type}."),
        };
    }

    private static RevocationEvidence ParseKernelWitnessFailure(
        JsonElement value,
        FrozenNodeId root)
    {
        RequireObjectFields(
            value,
            "KernelWitnessFailure evidence",
            "evidence_type", "failed_witness_id", "receipt_blob_oid", "receipt_sha256", "root_frozen_node_id");
        var witness = RequiredString(value, "failed_witness_id");
        if (!FrozenHashSyntax.IsSha256(witness))
        {
            throw new FormatException("KernelWitnessFailure has a malformed witness ID.");
        }

        return new RevocationEvidence.KernelWitnessFailure(
            root,
            WitnessId.Create(witness),
            RequiredString(value, "receipt_blob_oid"),
            RequiredString(value, "receipt_sha256"));
    }

    private static RevocationEvidence ParseAllowedAxiomRetired(
        JsonElement value,
        FrozenNodeId root)
    {
        RequireObjectFields(
            value,
            "AllowedAxiomRetired evidence",
            "axiom_name", "evidence_type", "receipt_blob_oid", "receipt_sha256", "root_frozen_node_id");
        return new RevocationEvidence.AllowedAxiomRetired(
            root,
            RequiredString(value, "axiom_name"),
            RequiredString(value, "receipt_blob_oid"),
            RequiredString(value, "receipt_sha256"));
    }

    private static RevocationEvidence ParseFormalContradiction(
        JsonElement value,
        FrozenNodeId root)
    {
        RequireObjectFields(
            value,
            "FormalContradictionCertificate evidence",
            "contradicted_statement_id", "evidence_type", "receipt_blob_oid", "receipt_sha256", "root_frozen_node_id");
        var statement = RequiredString(value, "contradicted_statement_id");
        if (!FrozenHashSyntax.IsSha256(statement))
        {
            throw new FormatException("FormalContradictionCertificate has a malformed statement ID.");
        }

        return new RevocationEvidence.FormalContradictionCertificate(
            root,
            StatementId.Create(statement),
            RequiredString(value, "receipt_blob_oid"),
            RequiredString(value, "receipt_sha256"));
    }

    private static RevocationEvidence ParseContentAddressMismatch(
        JsonElement value,
        FrozenNodeId root)
    {
        RequireObjectFields(
            value,
            "ContentAddressMismatch evidence",
            "actual_sha256", "evidence_type", "receipt_blob_oid", "receipt_sha256",
            "root_frozen_node_id");
        return new RevocationEvidence.ContentAddressMismatch(
            root,
            root.Value,
            RequiredString(value, "actual_sha256"),
            RequiredString(value, "receipt_blob_oid"),
            RequiredString(value, "receipt_sha256"));
    }

    private static string EvidenceSortKey(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item =>
            item.RootFrozenNodeId.Value + "\0" + nameof(RevocationEvidence.KernelWitnessFailure),
        RevocationEvidence.AllowedAxiomRetired item =>
            item.RootFrozenNodeId.Value + "\0" + nameof(RevocationEvidence.AllowedAxiomRetired),
        RevocationEvidence.FormalContradictionCertificate item =>
            item.RootFrozenNodeId.Value + "\0" + nameof(RevocationEvidence.FormalContradictionCertificate),
        RevocationEvidence.ContentAddressMismatch item =>
            item.RootFrozenNodeId.Value + "\0" + nameof(RevocationEvidence.ContentAddressMismatch),
        _ => throw new FormatException("Unknown revocation evidence variant."),
    };

    private static FrozenNodeId EvidenceRoot(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => item.RootFrozenNodeId,
        RevocationEvidence.AllowedAxiomRetired item => item.RootFrozenNodeId,
        RevocationEvidence.FormalContradictionCertificate item => item.RootFrozenNodeId,
        RevocationEvidence.ContentAddressMismatch item => item.RootFrozenNodeId,
        _ => throw new FormatException("Unknown revocation evidence variant."),
    };

    private static (string Oid, string Sha256) EvidenceReceipt(RevocationEvidence evidence) =>
        evidence switch
        {
            RevocationEvidence.KernelWitnessFailure item => (item.ReceiptBlobOid, item.ReceiptSha256),
            RevocationEvidence.AllowedAxiomRetired item => (item.ReceiptBlobOid, item.ReceiptSha256),
            RevocationEvidence.FormalContradictionCertificate item =>
                (item.ReceiptBlobOid, item.ReceiptSha256),
            RevocationEvidence.ContentAddressMismatch item => (item.ReceiptBlobOid, item.ReceiptSha256),
            _ => throw new FormatException("Unknown revocation evidence variant."),
        };

    private static ImmutableArray<FrozenNodeId> ParseFrozenNodeIds(JsonElement value, string name) =>
        RequiredStringArray(value, name)
            .Select(item => ParseFrozenNodeId(item, name))
            .ToImmutableArray();

    private static FrozenNodeId ParseFrozenNodeId(string value, string label) =>
        FrozenHashSyntax.IsSha256(value)
            ? FrozenNodeId.Create(value)
            : throw new FormatException($"{label} contains a malformed FrozenNodeId.");
}
