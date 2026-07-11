using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

public static partial class FrozenLedger
{
    private static FrozenRevokePayload ParseHistoricalRevoke(
        JsonElement payload,
        IEnumerable<FrozenLedgerEvent> events,
        IReadOnlyDictionary<string, FrozenActiveEntry> active,
        string priorHeadHash)
    {
        RequireObjectFields(
            payload,
            "Revoke payload",
            "affected_case_ids", "affected_frozen_node_ids", "closure_hash", "evidence",
            "graph_root", "root_case_ids", "root_frozen_node_ids");
        var affectedCases = RequiredStringArray(payload, "affected_case_ids");
        var affectedIds = ParseFrozenNodeIds(payload, "affected_frozen_node_ids");
        var rootCases = RequiredStringArray(payload, "root_case_ids");
        var rootIds = ParseFrozenNodeIds(payload, "root_frozen_node_ids");
        var evidenceElement = payload.GetProperty("evidence");
        if (evidenceElement.ValueKind != JsonValueKind.Array)
        {
            throw new FormatException("Revoke evidence must be an array.");
        }

        var evidence = evidenceElement.EnumerateArray().Select(ParseEvidence).ToImmutableArray();
        var evidenceKeys = evidence.Select(EvidenceSortKey).ToArray();
        if (!evidenceKeys.SequenceEqual(evidenceKeys.Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            throw new FormatException("Revoke evidence must be ordinal-sorted by root and variant.");
        }

        var evidenceRoots = evidence.Select(EvidenceRoot).ToImmutableArray();
        if (evidenceRoots.Distinct().Count() != evidenceRoots.Length
            || !evidenceRoots.OrderBy(static id => id.Value, StringComparer.Ordinal).SequenceEqual(rootIds))
        {
            throw new FormatException("Historical Revoke must carry exactly one evidence item per root.");
        }

        var activeById = active.Values.ToDictionary(
            static entry => entry.Material.FrozenNodeId,
            static entry => entry);
        foreach (var item in evidence)
        {
            ValidateHistoricalEvidence(item, activeById);
        }

        var closure = RevocationPlanner.ComputeClosure(events, active, rootIds);
        var expectedRootCases = rootIds.Select(id => activeById[id].Payload.CaseId)
            .Order(StringComparer.Ordinal)
            .ToImmutableArray();
        var closureHash = RequiredString(payload, "closure_hash");
        var graphRoot = RequiredString(payload, "graph_root");
        if (!FrozenHashSyntax.IsSha256(closureHash)
            || !FrozenHashSyntax.IsSha256(graphRoot)
            || !FrozenHashSyntax.IsSha256(priorHeadHash)
            || closureHash != closure.ClosureHash
            || !rootCases.SequenceEqual(expectedRootCases, StringComparer.Ordinal)
            || !affectedIds.SequenceEqual(closure.AffectedFrozenNodeIds)
            || !affectedCases.SequenceEqual(closure.AffectedCaseIds, StringComparer.Ordinal))
        {
            throw new FormatException(
                "Historical Revoke roots, evidence, graph, affected set, or closure hash is invalid.");
        }

        return new FrozenRevokePayload(
            affectedCases,
            affectedIds,
            closureHash,
            evidence,
            graphRoot,
            rootCases,
            rootIds);
    }

    private static void ValidateHistoricalEvidence(
        RevocationEvidence evidence,
        IReadOnlyDictionary<FrozenNodeId, FrozenActiveEntry> activeById)
    {
        var root = EvidenceRoot(evidence);
        if (!activeById.TryGetValue(root, out var entry))
        {
            throw new FormatException("Historical revocation evidence root is not active.");
        }

        var (receiptOid, receiptSha) = EvidenceReceipt(evidence);
        if (!FrozenHashSyntax.IsGitOid(receiptOid) || !FrozenHashSyntax.IsSha256(receiptSha))
        {
            throw new FormatException("Historical revocation evidence receipt address is malformed.");
        }

        switch (evidence)
        {
            case RevocationEvidence.KernelWitnessFailure failure
                when failure.FailedWitnessId != entry.Material.WitnessId:
                throw new FormatException("Historical KernelWitnessFailure does not bind its active witness.");
            case RevocationEvidence.FormalContradictionCertificate contradiction
                when contradiction.ContradictedStatementId != entry.Material.StatementId:
                throw new FormatException("Historical contradiction evidence does not bind its active statement.");
            case RevocationEvidence.AllowedAxiomRetired retired
                when string.IsNullOrWhiteSpace(retired.AxiomName):
                throw new FormatException("Historical axiom retirement evidence has no axiom name.");
            case RevocationEvidence.ContentAddressMismatch mismatch
                when mismatch.ExpectedSha256 != root.Value
                || !FrozenHashSyntax.IsSha256(mismatch.ActualSha256)
                || mismatch.ExpectedSha256 == mismatch.ActualSha256:
                throw new FormatException("Historical content mismatch does not bind its frozen root address.");
        }
    }

    private static FrozenNodeId EvidenceRoot(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => item.RootFrozenNodeId,
        RevocationEvidence.AllowedAxiomRetired item => item.RootFrozenNodeId,
        RevocationEvidence.FormalContradictionCertificate item => item.RootFrozenNodeId,
        RevocationEvidence.ContentAddressMismatch item => item.RootFrozenNodeId,
        _ => throw new FormatException("Unknown revocation evidence variant."),
    };

    private static (string Oid, string Sha256) EvidenceReceipt(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => (item.ReceiptBlobOid, item.ReceiptSha256),
        RevocationEvidence.AllowedAxiomRetired item => (item.ReceiptBlobOid, item.ReceiptSha256),
        RevocationEvidence.FormalContradictionCertificate item => (item.ReceiptBlobOid, item.ReceiptSha256),
        RevocationEvidence.ContentAddressMismatch item => (item.ReceiptBlobOid, item.ReceiptSha256),
        _ => throw new FormatException("Unknown revocation evidence variant."),
    };
}
