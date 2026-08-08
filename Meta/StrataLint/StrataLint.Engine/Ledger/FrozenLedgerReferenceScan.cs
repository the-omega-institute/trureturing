using System.Collections.Immutable;
using System.Text.Json;
using Dunet;

namespace StrataLint.Engine;

public sealed class FrozenLedgerReferenceSet
{
    private FrozenLedgerReferenceSet(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> revocationReceiptBlobOids,
        ImmutableArray<string> commitOids,
        ImmutableArray<string> treeOids,
        ImmutableArray<string> blobOids)
    {
        Inputs = inputs;
        RevocationReceiptBlobOids = revocationReceiptBlobOids;
        CommitOids = commitOids;
        TreeOids = treeOids;
        BlobOids = blobOids;
    }

    public ImmutableArray<FrozenLedgerInput> Inputs { get; }

    public ImmutableArray<string> RevocationReceiptBlobOids { get; }

    public ImmutableArray<string> CommitOids { get; }

    public ImmutableArray<string> TreeOids { get; }

    public ImmutableArray<string> BlobOids { get; }

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids)
    {
        var commits = inputs.Select(static input => input.BaseCommitOid);
        var trees = inputs.Select(static input => input.BaseTreeOid);
        var blobs = inputs.Select(static input => input.DescriptorBlobOid)
            .Concat(inputs.SelectMany(static input => input.SupportingBlobOids))
            .Concat(receiptOids);
        return Create(inputs, receiptOids, commits, trees, blobs);
    }

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> commitOids,
        IEnumerable<string> treeOids,
        IEnumerable<string> blobOids) =>
        new(
            inputs,
            receiptOids,
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
        "case_class", "case_id", "declaration_statement_ids", "evaluation", "expected",
        "frozen_node_id", "input", "input_fingerprint", "node_path", "prerequisite_frozen_node_ids",
        "semantic_receipt", "statement_id", "truth_state", "witness_id",
    ];

    internal static string[] LegacyReattestPayloadFields { get; } =
    [
        "case_id", "input", "input_fingerprint", "previous_attestation_event_hash", "semantic_receipt",
    ];

    internal static string[] ExtendedReattestPayloadFields { get; } =
    [
        "case_id", "declaration_statement_ids", "frozen_node_id", "input", "input_fingerprint",
        "prerequisite_frozen_node_ids", "previous_attestation_event_hash", "semantic_receipt",
        "statement_id", "witness_id",
    ];

    internal static string[] RevokePayloadFields { get; } =
    [
        "affected_case_ids", "affected_frozen_node_ids", "closure_hash", "evidence",
        "graph_root", "root_case_ids", "root_frozen_node_ids",
    ];

    internal static ImmutableDictionary<string, string[]> OidFields { get; } =
        new Dictionary<string, string[]>(StringComparer.Ordinal)
        {
            ["Genesis"] =
            [
                GeneratorBlobOid,
                OriginCommitOid,
                OriginTreeOid,
            ],
            ["Freeze"] =
            [
                "input.base_commit_oid",
                "input.base_tree_oid",
                "input.descriptor_blob_oid",
                "input.supporting_blob_oids",
            ],
            ["Reattest"] =
            [
                "input.base_commit_oid",
                "input.base_tree_oid",
                "input.descriptor_blob_oid",
                "input.supporting_blob_oids",
            ],
            ["Revoke"] =
            [
                "evidence[].receipt_blob_oid",
            ],
        }.ToImmutableDictionary(StringComparer.Ordinal);
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
    public static FrozenLedgerReferenceScanOutcome ScanReferences(FrozenLedgerSyntax syntax)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        try
        {
            ValidateSyntaxEnvelope(syntax);
            if (syntax.Lines.Length == 0)
            {
                throw new FormatException("Frozen ledger is empty.");
            }

            var inputs = ImmutableArray.CreateBuilder<FrozenLedgerInput>();
            var receipts = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var commits = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var trees = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var blobs = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            for (var index = 0; index < syntax.Lines.Length; index++)
            {
                var line = syntax.Lines[index];
                var root = line.Value;
                RequireObjectFields(
                    root,
                    "event envelope",
                    "event_hash", "event_type", "payload", "schema_version");
                RequireCanonicalLine(line);
                var eventHash = RequiredString(root, "event_hash");
                if (RequiredNonnegativeInteger(root, "schema_version") != 1
                    || !FrozenHashSyntax.IsSha256(eventHash)
                    || eventHash != ComputeEventHash(root))
                {
                    throw new FormatException("Frozen event schema/hash is invalid.");
                }

                var eventType = RequiredString(root, "event_type");
                if (!root.TryGetProperty("payload", out var payload)
                    || payload.ValueKind != JsonValueKind.Object)
                {
                    throw new FormatException("Frozen event payload must be an object.");
                }

                if (index == 0 && eventType != "Genesis")
                {
                    throw new FormatException("Sequence zero must be Genesis.");
                }

                if (eventType == "Genesis")
                {
                    if (index != 0)
                    {
                        throw new FormatException("Genesis may occur only at sequence zero.");
                    }

                    RequireObjectFields(
                        payload,
                        "Genesis payload",
                        FrozenLedgerReferenceProjection.GenesisPayloadFields);
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
                    RequireEventPayloadFields(payload, eventType);
                    if (!payload.TryGetProperty("input", out var input))
                    {
                        throw new FormatException($"{eventType} payload is missing input fields.");
                    }

                    var parsed = ParseInput(input);
                    inputs.Add(parsed);
                    AddInputReferences(parsed, commits, trees, blobs);
                }
                else if (eventType == "Revoke")
                {
                    RequireObjectFields(
                        payload,
                        "Revoke payload",
                        FrozenLedgerReferenceProjection.RevokePayloadFields);
                    if (!payload.TryGetProperty("evidence", out var evidence)
                        || evidence.ValueKind != JsonValueKind.Array)
                    {
                        throw new FormatException("Revoke payload is missing evidence fields.");
                    }

                    foreach (var item in evidence.EnumerateArray().Select(ParseEvidence))
                    {
                        var (oid, _) = EvidenceReceipt(item);
                        if (!FrozenHashSyntax.IsGitOid(oid))
                        {
                            throw new FormatException("Revoke evidence receipt has a malformed Git blob OID.");
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
        catch (Exception exception) when (
            exception is FormatException or JsonException or InvalidOperationException or KeyNotFoundException)
        {
            return new FrozenLedgerReferenceScanOutcome.Rejected(exception.Message);
        }
    }

    private static void RequireEventPayloadFields(JsonElement payload, string eventType)
    {
        if (eventType == "Freeze")
        {
            RequireObjectFields(
                payload,
                "Freeze payload",
                FrozenLedgerReferenceProjection.FreezePayloadFields);
            return;
        }

        if (HasExactObjectFields(payload, FrozenLedgerReferenceProjection.LegacyReattestPayloadFields))
        {
            return;
        }

        RequireObjectFields(
            payload,
            "Reattest payload",
            FrozenLedgerReferenceProjection.ExtendedReattestPayloadFields);
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
