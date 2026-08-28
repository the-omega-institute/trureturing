using System.Collections.Immutable;
using System.Text.Json;
using Dunet;

namespace StrataLint.Engine;

public sealed class FrozenLedgerReferenceSet
{
    private FrozenLedgerReferenceSet(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> revocationReceiptBlobOids,
        ImmutableArray<string> requiredAncestorCommitOids,
        ImmutableArray<string> commitOids,
        ImmutableArray<string> treeOids,
        ImmutableArray<string> blobOids)
    {
        Inputs = inputs;
        RevocationReceiptBlobOids = revocationReceiptBlobOids;
        RequiredAncestorCommitOids = requiredAncestorCommitOids;
        CommitOids = commitOids;
        TreeOids = treeOids;
        BlobOids = blobOids;
    }

    public ImmutableArray<FrozenLedgerInput> Inputs { get; }

    public ImmutableArray<string> RevocationReceiptBlobOids { get; }

    internal ImmutableArray<string> RequiredAncestorCommitOids { get; }

    public ImmutableArray<string> CommitOids { get; }

    public ImmutableArray<string> TreeOids { get; }

    public ImmutableArray<string> BlobOids { get; }

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids) =>
        Create(inputs, receiptOids, []);

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> requiredAncestorCommitOids)
    {
        var commits = inputs.Select(static input => input.BaseCommitOid);
        var trees = inputs.Select(static input => input.BaseTreeOid);
        var blobs = inputs.Select(static input => input.DescriptorBlobOid)
            .Concat(inputs.SelectMany(static input => input.SupportingBlobOids))
            .Concat(receiptOids);
        return Create(
            inputs,
            receiptOids,
            requiredAncestorCommitOids,
            commits,
            trees,
            blobs);
    }

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> commitOids,
        IEnumerable<string> treeOids,
        IEnumerable<string> blobOids) =>
        Create(
            inputs,
            receiptOids,
            [],
            commitOids,
            treeOids,
            blobOids);

    private static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> requiredAncestorCommitOids,
        IEnumerable<string> commitOids,
        IEnumerable<string> treeOids,
        IEnumerable<string> blobOids) =>
        new(
            inputs,
            receiptOids,
            Sorted(requiredAncestorCommitOids),
            Sorted(commitOids),
            Sorted(treeOids),
            Sorted(blobOids));

    private static ImmutableArray<string> Sorted(IEnumerable<string> values) =>
        values.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToImmutableArray();
}

internal static class FrozenLedgerReferenceProjection
{
    internal const string GeneratorBlobOid = "generator_blob_oid";
    internal const string OriginCommitOid = "origin_commit_oid";
    internal const string OriginTreeOid = "origin_tree_oid";

    internal static string[] GenesisPayloadFields { get; } =
    [
        GeneratorBlobOid, OriginCommitOid, OriginTreeOid, "protocol_version", "rule_catalog_root",
    ];

    internal static string[] FreezePayloadFields { get; } =
    [
        "axiom_closure", "case_id", "declaration_statement_ids", "frozen_node_id", "input",
        "prerequisite_frozen_node_ids", "statement_id", "witness_id",
    ];

    internal static string[] RevokePayloadFields { get; } =
    [
        "affected_case_ids", "affected_frozen_node_ids", "closure_hash", "evidence",
        "graph_root", "root_case_ids",
    ];

}

[Union(EnableImplicitConversions = false)]
public partial record FrozenLedgerReferenceScanOutcome
{
    public partial record Accepted
    {
        internal Accepted(FrozenLedgerReferenceSet references) =>
            References = references ?? throw new ArgumentNullException(nameof(references));

        public FrozenLedgerReferenceSet References { get; }
    }

    public partial record Rejected(string Message);
}

public static partial class FrozenLedger
{
    internal static FrozenLedgerInput? ParseAcceptedEventInput(
        string eventType,
        JsonElement payload)
    {
        if (eventType == "Genesis")
        {
            RequireObjectFields(
                payload,
                "Genesis payload",
                FrozenLedgerReferenceProjection.GenesisPayloadFields);
            return null;
        }

        if (eventType == "Freeze")
        {
            RequireEventPayloadFields(payload, eventType);
            if (!payload.TryGetProperty("input", out var input))
            {
                throw new FormatException($"{eventType} payload is missing input fields.");
            }

            return ParseInput(input);
        }

        if (eventType == "Revoke")
        {
            RequireObjectFields(
                payload,
                "Revoke payload",
                FrozenLedgerReferenceProjection.RevokePayloadFields);
            return null;
        }

        throw new FormatException($"Unknown frozen event type {eventType}.");
    }

    public static FrozenLedgerReferenceScanOutcome ScanReferences(
        ImmutableArray<DagLedgerFileEvent> events)
    {
        try
        {
            if (events.IsDefaultOrEmpty)
            {
                throw new FormatException("Frozen ledger is empty.");
            }

            return ScanReferenceEvents(events);
        }
        catch (Exception exception) when (
            exception is FormatException or JsonException or InvalidOperationException or KeyNotFoundException)
        {
            return new FrozenLedgerReferenceScanOutcome.Rejected(exception.Message);
        }
    }

    private static FrozenLedgerReferenceScanOutcome.Accepted ScanReferenceEvents(
        IEnumerable<DagLedgerFileEvent> events)
    {
        var inputs = ImmutableArray.CreateBuilder<FrozenLedgerInput>();
        var receipts = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var commits = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var trees = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var blobs = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        foreach (var item in events)
        {
            var eventType = item.EventType;
            var payload = item.Payload;
            FrozenLedgerBaseViewReader.ValidateTrustedPayload(
                eventType,
                item.SchemaVersion,
                payload);

            if (eventType == "Genesis")
            {
                AddOid(
                    blobs,
                    RequiredString(payload, FrozenLedgerReferenceProjection.GeneratorBlobOid),
                    "Genesis generator blob");
                AddOid(
                    commits,
                    RequiredString(payload, FrozenLedgerReferenceProjection.OriginCommitOid),
                    "Genesis origin commit");
                AddOid(
                    trees,
                    RequiredString(payload, FrozenLedgerReferenceProjection.OriginTreeOid),
                    "Genesis origin tree");
            }
            else if (eventType is "Freeze" or "Reattest")
            {
                var parsed = item.Input
                    ?? throw new FormatException($"{eventType} payload is missing input fields.");

                inputs.Add(parsed);
                AddInputReferences(parsed, commits, trees, blobs);
            }
            else if (eventType == "Revoke")
            {
                var evidence = payload.GetProperty("evidence");
                if (evidence.ValueKind != JsonValueKind.Array)
                {
                    throw new FormatException("Revoke payload is missing evidence fields.");
                }

                foreach (var evidenceItem in evidence.EnumerateArray().Select(ParseEvidence))
                {
                    var (oid, _) = EvidenceReceipt(evidenceItem);
                    if (!FrozenHashSyntax.IsGitOid(oid))
                    {
                        throw new FormatException(
                            "Revoke evidence receipt has a malformed Git blob OID.");
                    }

                    receipts.Add(oid);
                    blobs.Add(oid);
                }
            }
            else
            {
                throw new FormatException($"Unknown frozen event type {eventType}.");
            }
        }

        return new FrozenLedgerReferenceScanOutcome.Accepted(FrozenLedgerReferenceSet.Create(
            inputs.ToImmutable(),
            receipts.Order(StringComparer.Ordinal).ToImmutableArray(),
            commits,
            trees,
            blobs));
    }

    private static void RequireEventPayloadFields(
        JsonElement payload,
        string eventType)
    {
        if (eventType != "Freeze")
        {
            throw new FormatException($"Unknown frozen event type {eventType}.");
        }

        RequireObjectFields(
            payload,
            "Freeze payload",
            FrozenLedgerReferenceProjection.FreezePayloadFields);
    }

    private static void AddInputReferences(
        FrozenLedgerInput input,
        ISet<string> commits,
        ISet<string> trees,
        ISet<string> blobs)
    {
        commits.Add(input.BaseCommitOid);
        trees.Add(input.BaseTreeOid);
        blobs.Add(input.DescriptorBlobOid);
        blobs.UnionWith(input.SupportingBlobOids);
    }

    private static void AddOid(ISet<string> target, string oid, string label)
    {
        if (!FrozenHashSyntax.IsGitOid(oid))
        {
            throw new FormatException($"{label} has a malformed Git object OID.");
        }

        target.Add(oid);
    }
}
