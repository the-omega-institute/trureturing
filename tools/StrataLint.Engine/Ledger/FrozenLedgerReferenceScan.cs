using System.Collections.Immutable;
using System.Text.Json;
using Dunet;

namespace StrataLint.Engine;

public sealed class FrozenLedgerReferenceSet
{
    private FrozenLedgerReferenceSet(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<FrozenEnvironmentReference> environmentReferences,
        ImmutableArray<string> revocationReceiptBlobOids,
        ImmutableArray<string> requiredAncestorCommitOids,
        ImmutableArray<string> commitOids,
        ImmutableArray<string> treeOids,
        ImmutableArray<string> blobOids)
    {
        Inputs = inputs;
        EnvironmentReferences = environmentReferences;
        RevocationReceiptBlobOids = revocationReceiptBlobOids;
        RequiredAncestorCommitOids = requiredAncestorCommitOids;
        CommitOids = commitOids;
        TreeOids = treeOids;
        BlobOids = blobOids;
    }

    public ImmutableArray<FrozenLedgerInput> Inputs { get; }

    public ImmutableArray<FrozenEnvironmentReference> EnvironmentReferences { get; }

    public ImmutableArray<string> RevocationReceiptBlobOids { get; }

    internal ImmutableArray<string> RequiredAncestorCommitOids { get; }

    public ImmutableArray<string> CommitOids { get; }

    public ImmutableArray<string> TreeOids { get; }

    public ImmutableArray<string> BlobOids { get; }

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids) =>
        Create(inputs, ImmutableArray<FrozenEnvironmentReference>.Empty, receiptOids);

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> commitOids,
        IEnumerable<string> treeOids,
        IEnumerable<string> blobOids) =>
        Create(
            inputs,
            ImmutableArray<FrozenEnvironmentReference>.Empty,
            receiptOids,
            commitOids,
            treeOids,
            blobOids);

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<FrozenEnvironmentReference> environmentReferences,
        ImmutableArray<string> receiptOids)
        => Create(inputs, environmentReferences, receiptOids, []);

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<FrozenEnvironmentReference> environmentReferences,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> requiredAncestorCommitOids)
    {
        var commits = inputs.Select(static input => input.BaseCommitOid);
        var trees = inputs.Select(static input => input.BaseTreeOid);
        var blobs = inputs.Select(static input => input.DescriptorBlobOid)
            .Concat(inputs.SelectMany(static input => input.SupportingBlobOids))
            .Concat(environmentReferences.SelectMany(static reference => new[]
            {
                reference.Environment.LakeManifestBlobOid,
                reference.Environment.LakefileBlobOid,
                reference.Environment.LeanToolchainBlobOid,
            }))
            .Concat(receiptOids);
        return Create(
            inputs,
            environmentReferences,
            receiptOids,
            requiredAncestorCommitOids,
            commits,
            trees,
            blobs);
    }

    internal static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<FrozenEnvironmentReference> environmentReferences,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> commitOids,
        IEnumerable<string> treeOids,
        IEnumerable<string> blobOids) =>
        Create(
            inputs,
            environmentReferences,
            receiptOids,
            [],
            commitOids,
            treeOids,
            blobOids);

    private static FrozenLedgerReferenceSet Create(
        ImmutableArray<FrozenLedgerInput> inputs,
        ImmutableArray<FrozenEnvironmentReference> environmentReferences,
        ImmutableArray<string> receiptOids,
        IEnumerable<string> requiredAncestorCommitOids,
        IEnumerable<string> commitOids,
        IEnumerable<string> treeOids,
        IEnumerable<string> blobOids) =>
        new(
            inputs,
            environmentReferences,
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
        "case_class", "case_id", "declaration_statement_ids", "evaluation", "expected",
        "frozen_node_id", "input", "input_fingerprint", "node_path", "prerequisite_frozen_node_ids",
        "semantic_receipt", "statement_id", "truth_state", "witness_id",
    ];

    internal static string[] FreezePayloadFieldsV3 { get; } =
    [
        "axiom_closure", "case_class", "case_id", "declaration_statement_ids", "evaluation", "expected",
        "frozen_node_id", "input", "input_fingerprint", "node_path", "prerequisite_frozen_node_ids",
        "semantic_receipt", "statement_id", "truth_state", "witness_id",
    ];

    internal static string[] FreezePayloadFieldsV4 { get; } =
    [
        "axiom_closure", "case_id", "declaration_statement_ids", "frozen_node_id", "input",
        "prerequisite_frozen_node_ids", "statement_id", "witness_id",
    ];

    internal static string[] LegacyReattestPayloadFields { get; } =
    [
        "case_id", "input", "input_fingerprint", "previous_attestation_event_hash", "semantic_receipt",
    ];

    internal static string[] LegacyReattestPayloadFieldsV3 { get; } =
    [
        "axiom_closure", "case_id", "input", "input_fingerprint",
        "previous_attestation_event_hash", "semantic_receipt",
    ];

    internal static string[] ExtendedReattestPayloadFields { get; } =
    [
        "case_id", "declaration_statement_ids", "frozen_node_id", "input", "input_fingerprint",
        "prerequisite_frozen_node_ids", "previous_attestation_event_hash", "semantic_receipt",
        "statement_id", "witness_id",
    ];

    internal static string[] ExtendedReattestPayloadFieldsV3 { get; } =
    [
        "axiom_closure", "case_id", "declaration_statement_ids", "frozen_node_id", "input",
        "input_fingerprint", "prerequisite_frozen_node_ids", "previous_attestation_event_hash",
        "semantic_receipt", "statement_id", "witness_id",
    ];

    internal static string[] LegacyReattestPayloadFieldsV4 { get; } =
    [
        "axiom_closure", "case_id", "input", "previous_attestation_event_hash",
    ];

    internal static string[] ExtendedReattestPayloadFieldsV4 { get; } =
    [
        "axiom_closure", "case_id", "declaration_statement_ids", "frozen_node_id", "input",
        "prerequisite_frozen_node_ids", "previous_attestation_event_hash", "statement_id", "witness_id",
    ];

    internal static string[] RevokePayloadFields { get; } =
    [
        "affected_case_ids", "affected_frozen_node_ids", "closure_hash", "evidence",
        "graph_root", "root_case_ids",
    ];

    internal static string[] SupersedePayloadFields { get; } =
    [
        "axiom_closure", "case_id", "declaration_statement_ids", "environment",
        "frozen_node_id", "input", "prerequisite_frozen_node_ids",
        "previous_attestation_event_hash", "statement_id", "witness_id",
    ];

}

public sealed record FrozenEnvironmentReference(
    FrozenLedgerInput Input,
    FrozenEnvironmentPins Environment);

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
        JsonElement payload,
        int schemaVersion)
    {
        if (eventType == "Genesis")
        {
            RequireObjectFields(
                payload,
                "Genesis payload",
                FrozenLedgerReferenceProjection.GenesisPayloadFields);
            return null;
        }

        if (eventType is "Freeze" or "Reattest")
        {
            RequireEventPayloadFields(payload, eventType, schemaVersion);
            if (!payload.TryGetProperty("input", out var input))
            {
                throw new FormatException($"{eventType} payload is missing input fields.");
            }

            return ParseInput(input);
        }

        if (eventType == SupersedeEventType)
        {
            return ParseSupersede(payload).Input;
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
            var environmentReferences = ImmutableArray.CreateBuilder<FrozenEnvironmentReference>();
            var receipts = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var commits = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var trees = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var blobs = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var previous = ZeroHash;
            for (var index = 0; index < syntax.Lines.Length; index++)
            {
                var line = syntax.Lines[index];
                var root = line.Value;
                RequireObjectFields(
                    root,
                    "event envelope",
                    "event_hash", "event_type", "payload", "previous_hash", "schema_version", "sequence");
                RequireCanonicalLine(line);
                var sequence = RequiredNonnegativeInteger(root, "sequence");
                var previousHash = RequiredString(root, "previous_hash");
                var eventHash = RequiredString(root, "event_hash");
                if (sequence != index
                    || RequiredNonnegativeInteger(root, "schema_version") != 1
                    || previousHash != previous
                    || !FrozenHashSyntax.IsSha256(eventHash)
                    || eventHash != ComputeEventHash(root))
                {
                    throw new FormatException("Frozen event sequence/hash chain is invalid.");
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
                else if (eventType == SupersedeEventType)
                {
                    var supersede = ParseSupersede(payload);
                    inputs.Add(supersede.Input);
                    environmentReferences.Add(new FrozenEnvironmentReference(
                        supersede.Input,
                        supersede.Environment));
                    AddInputReferences(supersede.Input, commits, trees, blobs);
                }
                else
                {
                    throw new FormatException($"Unknown frozen event type {eventType}.");
                }

                previous = eventHash;
            }

            return new FrozenLedgerReferenceScanOutcome.Accepted(FrozenLedgerReferenceSet.Create(
                inputs.ToImmutable(),
                environmentReferences.ToImmutable(),
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

    internal static FrozenLedgerReferenceScanOutcome ScanSuffixReferences(
        FrozenLedgerSyntax syntax,
        int startIndex,
        int sequenceOffset,
        string previousHash)
    {
        ArgumentNullException.ThrowIfNull(syntax);
        try
        {
            if (startIndex < 0 || startIndex > syntax.Lines.Length)
            {
                throw new ArgumentOutOfRangeException(nameof(startIndex));
            }

            ValidateSuffixSyntaxEnvelope(syntax, startIndex);

            var inputs = ImmutableArray.CreateBuilder<FrozenLedgerInput>();
            var environmentReferences = ImmutableArray.CreateBuilder<FrozenEnvironmentReference>();
            var receipts = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var commits = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var trees = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var blobs = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
            var previous = previousHash;
            for (var index = startIndex; index < syntax.Lines.Length; index++)
            {
                var line = syntax.Lines[index];
                var root = line.Value;
                RequireObjectFields(
                    root,
                    "event envelope",
                    "event_hash", "event_type", "payload", "previous_hash", "schema_version", "sequence");
                RequireCanonicalLine(line);
                var sequence = RequiredNonnegativeInteger(root, "sequence");
                var recordedPrevious = RequiredString(root, "previous_hash");
                var eventHash = RequiredString(root, "event_hash");
                if (sequence != sequenceOffset + index
                    || RequiredNonnegativeInteger(root, "schema_version") != 1
                    || !string.Equals(recordedPrevious, previous, StringComparison.Ordinal)
                    || !FrozenHashSyntax.IsSha256(eventHash)
                    || !string.Equals(eventHash, ComputeEventHash(root), StringComparison.Ordinal))
                {
                    throw new FormatException("Frozen suffix sequence/hash chain is invalid.");
                }

                var eventType = RequiredString(root, "event_type");
                var payload = root.GetProperty("payload");
                if (eventType is "Freeze" or "Reattest")
                {
                    RequireEventPayloadFields(payload, eventType);
                    var parsed = ParseInput(payload.GetProperty("input"));
                    inputs.Add(parsed);
                    AddInputReferences(parsed, commits, trees, blobs);
                }
                else if (eventType == "Revoke")
                {
                    RequireObjectFields(
                        payload,
                        "Revoke payload",
                        FrozenLedgerReferenceProjection.RevokePayloadFields);
                    var evidence = payload.GetProperty("evidence");
                    if (evidence.ValueKind != JsonValueKind.Array)
                    {
                        throw new FormatException("Revoke payload is missing evidence fields.");
                    }

                    foreach (var item in evidence.EnumerateArray().Select(ParseEvidence))
                    {
                        var (oid, _) = EvidenceReceipt(item);
                        if (!FrozenHashSyntax.IsGitOid(oid))
                        {
                            throw new FormatException(
                                "Revoke evidence receipt has a malformed Git blob OID.");
                        }

                        receipts.Add(oid);
                        blobs.Add(oid);
                    }
                }
                else if (eventType == SupersedeEventType)
                {
                    var supersede = ParseSupersede(payload);
                    inputs.Add(supersede.Input);
                    environmentReferences.Add(new FrozenEnvironmentReference(
                        supersede.Input,
                        supersede.Environment));
                    AddInputReferences(supersede.Input, commits, trees, blobs);
                }
                else
                {
                    throw new FormatException(
                        $"Event type {eventType} is not legal in a candidate suffix.");
                }

                previous = eventHash;
            }

            return new FrozenLedgerReferenceScanOutcome.Accepted(FrozenLedgerReferenceSet.Create(
                inputs.ToImmutable(),
                environmentReferences.ToImmutable(),
                receipts.Order(StringComparer.Ordinal).ToImmutableArray(),
                commits,
                trees,
                blobs));
        }
        catch (Exception exception) when (
            exception is ArgumentOutOfRangeException
                or FormatException
                or JsonException
                or InvalidOperationException
                or KeyNotFoundException)
        {
            return new FrozenLedgerReferenceScanOutcome.Rejected(exception.Message);
        }
    }

    private static void RequireEventPayloadFields(
        JsonElement payload,
        string eventType,
        int? schemaVersion = null)
    {
        if (eventType == "Freeze")
        {
            if (schemaVersion is null
                && (HasExactObjectFields(payload, FrozenLedgerReferenceProjection.FreezePayloadFields)
                    || HasExactObjectFields(payload, FrozenLedgerReferenceProjection.FreezePayloadFieldsV3)
                    || HasExactObjectFields(payload, FrozenLedgerReferenceProjection.FreezePayloadFieldsV4)))
            {
                return;
            }

            RequireObjectFields(
                payload,
                "Freeze payload",
                schemaVersion switch
                {
                    3 => FrozenLedgerReferenceProjection.FreezePayloadFieldsV3,
                    4 => FrozenLedgerReferenceProjection.FreezePayloadFieldsV4,
                    _ => FrozenLedgerReferenceProjection.FreezePayloadFields,
                });
            return;
        }

        var allowed = schemaVersion switch
        {
            2 => new[]
            {
                FrozenLedgerReferenceProjection.LegacyReattestPayloadFields,
                FrozenLedgerReferenceProjection.ExtendedReattestPayloadFields,
            },
            3 => new[]
            {
                FrozenLedgerReferenceProjection.LegacyReattestPayloadFieldsV3,
                FrozenLedgerReferenceProjection.ExtendedReattestPayloadFieldsV3,
            },
            4 => new[]
            {
                FrozenLedgerReferenceProjection.LegacyReattestPayloadFieldsV4,
                FrozenLedgerReferenceProjection.ExtendedReattestPayloadFieldsV4,
            },
            _ => new[]
            {
                FrozenLedgerReferenceProjection.LegacyReattestPayloadFields,
                FrozenLedgerReferenceProjection.ExtendedReattestPayloadFields,
                FrozenLedgerReferenceProjection.LegacyReattestPayloadFieldsV3,
                FrozenLedgerReferenceProjection.ExtendedReattestPayloadFieldsV3,
                FrozenLedgerReferenceProjection.LegacyReattestPayloadFieldsV4,
                FrozenLedgerReferenceProjection.ExtendedReattestPayloadFieldsV4,
            },
        };
        if (allowed.Any(fields => HasExactObjectFields(payload, fields)))
        {
            return;
        }

        RequireObjectFields(
            payload,
            "Reattest payload",
            schemaVersion switch
            {
                2 => FrozenLedgerReferenceProjection.ExtendedReattestPayloadFields,
                4 => FrozenLedgerReferenceProjection.ExtendedReattestPayloadFieldsV4,
                _ => FrozenLedgerReferenceProjection.ExtendedReattestPayloadFieldsV3,
            });
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
