using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text.Json;
using Dunet;
using Trureturing.Truth;

namespace StrataLint.Engine;

public static class RevocationReceiptWriter
{
    public static ImmutableArray<byte> Write(
        FrozenLedgerConsistent baseline,
        RevocationEvidence evidence)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(evidence);
        TrustedRevocationReceiptStore.ValidateClaim(baseline, evidence);
        return Write(baseline.HeadHash, baseline.GraphRoot, evidence);
    }

    internal static ImmutableArray<byte> Write(
        string baselineHeadHash,
        string baselineGraphRoot,
        RevocationEvidence evidence)
    {
        var value = evidence switch
        {
            RevocationEvidence.KernelWitnessFailure item => JsonSerializer.SerializeToElement(new
            {
                baseline_graph_root = baselineGraphRoot,
                baseline_head_hash = baselineHeadHash,
                evidence_type = nameof(RevocationEvidence.KernelWitnessFailure),
                failed_statement_id = item.FailedStatementId.Value,
                kind = "revocation-receipt",
                root_frozen_node_id = item.RootFrozenNodeId.Value,
                schema_version = 2,
            }),
            RevocationEvidence.AllowedAxiomRetired item => JsonSerializer.SerializeToElement(new
            {
                axiom_name = item.AxiomName,
                baseline_graph_root = baselineGraphRoot,
                baseline_head_hash = baselineHeadHash,
                evidence_type = nameof(RevocationEvidence.AllowedAxiomRetired),
                kind = "revocation-receipt",
                root_frozen_node_id = item.RootFrozenNodeId.Value,
                schema_version = 2,
            }),
            RevocationEvidence.FormalContradictionCertificate item => JsonSerializer.SerializeToElement(new
            {
                baseline_graph_root = baselineGraphRoot,
                baseline_head_hash = baselineHeadHash,
                contradicted_statement_id = item.ContradictedStatementId.Value,
                evidence_type = nameof(RevocationEvidence.FormalContradictionCertificate),
                kind = "revocation-receipt",
                root_frozen_node_id = item.RootFrozenNodeId.Value,
                schema_version = 2,
            }),
            RevocationEvidence.ContentAddressMismatch item => JsonSerializer.SerializeToElement(new
            {
                actual_sha256 = item.ActualSha256,
                baseline_graph_root = baselineGraphRoot,
                baseline_head_hash = baselineHeadHash,
                evidence_type = nameof(RevocationEvidence.ContentAddressMismatch),
                expected_sha256 = item.ExpectedSha256,
                kind = "revocation-receipt",
                root_frozen_node_id = item.RootFrozenNodeId.Value,
                schema_version = 2,
            }),
            _ => throw new FormatException("Unknown revocation evidence variant."),
        };
        return StructuredCanonicalWriter.WriteJson(value);
    }
}

public sealed class TrustedRevocationReceiptStore
{
    private readonly ImmutableDictionary<string, TrustedReceipt> byOid;

    private enum ValidationMode
    {
        Candidate,
        TrustedBase,
    }

    private TrustedRevocationReceiptStore(
        string baselineHeadHash,
        string baselineGraphRoot,
        ImmutableDictionary<string, TrustedReceipt> byOid)
    {
        BaselineHeadHash = baselineHeadHash;
        BaselineGraphRoot = baselineGraphRoot;
        this.byOid = byOid;
    }

    internal string BaselineHeadHash { get; }

    internal string BaselineGraphRoot { get; }

    internal static TrustedRevocationReceiptStore Empty(FrozenLedgerConsistent baseline) =>
        new(
            baseline.HeadHash,
            baseline.GraphRoot,
            ImmutableDictionary<string, TrustedReceipt>.Empty);

    public static RevocationReceiptStoreOutcome Materialize(
        FrozenLedgerConsistent baseline,
        RepositorySnapshot protectedSnapshot,
        IEnumerable<string> requestedBlobOids) =>
        Materialize(
            baseline,
            protectedSnapshot,
            requestedBlobOids,
            static (bytes, algorithm) =>
                FrozenContentAddress.ComputeGitBlobOid(bytes.AsSpan(), algorithm));

    internal static RevocationReceiptStoreOutcome Materialize(
        FrozenLedgerConsistent baseline,
        RepositorySnapshot protectedSnapshot,
        IEnumerable<string> requestedBlobOids,
        Func<ImmutableArray<byte>, HashAlgorithmName, string> computeGitBlobOid)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(protectedSnapshot);
        ArgumentNullException.ThrowIfNull(requestedBlobOids);
        try
        {
            var requested = requestedBlobOids
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToImmutableArray();
            if (requested.Any(static oid => !FrozenHashSyntax.IsGitOid(oid)))
            {
                throw new FormatException("Revocation receipt request contains a malformed Git blob OID.");
            }

            var filesByOid = protectedSnapshot.Files.Values
                .Where(static file => file.GitBlobOid is not null)
                .GroupBy(static file => file.GitBlobOid!, StringComparer.Ordinal)
                .ToDictionary(
                    static group => group.Key,
                    static group => group.First(),
                    StringComparer.Ordinal);

            var receipts = ImmutableDictionary.CreateBuilder<string, TrustedReceipt>(StringComparer.Ordinal);
            foreach (var oid in requested)
            {
                if (!filesByOid.TryGetValue(oid, out var file))
                {
                    throw new FormatException(
                        $"Revocation receipt {oid} is not a blob in the protected baseline snapshot.");
                }

                var bytes = file.RawBytes;
                var evidence = ParseReceipt(bytes, ValidationMode.TrustedBase);
                var sha = "sha256:" + Convert.ToHexStringLower(SHA256.HashData(bytes.AsSpan()));
                receipts.Add(oid, new TrustedReceipt(bytes, sha, WithReceiptAddress(evidence, oid, sha)));
            }

            return new RevocationReceiptStoreOutcome.Accepted(new TrustedRevocationReceiptStore(
                baseline.HeadHash,
                baseline.GraphRoot,
                receipts.ToImmutable()));
        }
        catch (Exception exception) when (
            exception is FormatException or JsonException or InvalidOperationException)
        {
            return new RevocationReceiptStoreOutcome.Rejected(exception.Message);
        }
    }

    internal bool Authorizes(RevocationEvidence evidence, out string message)
    {
        var (oid, sha) = ReceiptAddress(evidence);
        if (!byOid.TryGetValue(oid, out var receipt)
            || receipt.Sha256 != sha
            || !SameClaim(receipt.Evidence, evidence))
        {
            message = "Revocation evidence does not match a typed receipt from the protected baseline.";
            return false;
        }

        message = string.Empty;
        return true;
    }

    internal ImmutableArray<RevocationEvidence> Evidence => byOid
        .OrderBy(static item => item.Key, StringComparer.Ordinal)
        .Select(static item => item.Value.Evidence)
        .ToImmutableArray();

    internal static string ReceiptBlobOid(RevocationEvidence evidence) =>
        ReceiptAddress(evidence).Oid;

    internal static void ValidateClaim(FrozenLedgerConsistent baseline, RevocationEvidence evidence)
    {
        var root = EvidenceRoot(evidence);
        var entry = baseline.ActiveEntries.Values.SingleOrDefault(
            item => item.Material.FrozenNodeId == root)
            ?? throw new FormatException("Revocation receipt root is not active frozen material.");
        switch (evidence)
        {
            case RevocationEvidence.KernelWitnessFailure failure
                when failure.FailedStatementId != entry.Material.StatementId:
                throw new FormatException("KernelWitnessFailure receipt does not bind the active statement.");
            case RevocationEvidence.AllowedAxiomRetired retired
                when string.IsNullOrWhiteSpace(retired.AxiomName)
                || !entry.Material.AxiomClosure.Contains(retired.AxiomName, StringComparer.Ordinal):
                throw new FormatException("AllowedAxiomRetired receipt does not bind the active axiom closure.");
            case RevocationEvidence.FormalContradictionCertificate contradiction
                when contradiction.ContradictedStatementId != entry.Material.StatementId:
                throw new FormatException("Contradiction receipt does not bind the active statement.");
            case RevocationEvidence.ContentAddressMismatch mismatch
                when mismatch.ExpectedSha256 != entry.Material.FrozenNodeId.Value
                || !FrozenHashSyntax.IsSha256(mismatch.ActualSha256)
                || mismatch.ExpectedSha256 == mismatch.ActualSha256:
                throw new FormatException("Content mismatch receipt does not bind the active frozen address.");
        }
    }

    internal static void ValidateCandidateReceipt(
        FrozenLedgerConsistent baseline,
        ImmutableArray<byte> bytes) =>
        _ = ParseAndValidateReceipt(baseline, bytes);

    private static RevocationEvidence ParseReceipt(
        ImmutableArray<byte> bytes,
        ValidationMode validationMode)
    {
        if (validationMode is ValidationMode.Candidate
            && (bytes.Length == 0
                || bytes[^1] != (byte)'\n'
                || bytes.AsSpan().Contains((byte)'\r')))
        {
            throw new FormatException("Revocation receipt must be one LF-terminated JSON object.");
        }

        using var document = JsonDocument.Parse(bytes.AsMemory());
        var root = document.RootElement;
        var type = String(root, "evidence_type");
        var evidenceRoot = FrozenNode(String(root, "root_frozen_node_id"));
        var evidence = type switch
        {
            nameof(RevocationEvidence.KernelWitnessFailure) => ParseKernel(root, evidenceRoot),
            nameof(RevocationEvidence.AllowedAxiomRetired) => ParseAxiom(root, evidenceRoot),
            nameof(RevocationEvidence.FormalContradictionCertificate) => ParseContradiction(root, evidenceRoot),
            nameof(RevocationEvidence.ContentAddressMismatch) => ParseMismatch(root, evidenceRoot),
            _ => throw new FormatException($"Unknown typed revocation receipt {type}."),
        };
        if (String(root, "kind") != "revocation-receipt"
            || Integer(root, "schema_version") != 2)
        {
            throw new FormatException("Revocation receipt has an unsupported kind or schema version.");
        }

        return evidence;
    }

    private static RevocationEvidence ParseAndValidateReceipt(
        FrozenLedgerConsistent baseline,
        ImmutableArray<byte> bytes)
    {
        var evidence = ParseReceipt(bytes, ValidationMode.Candidate);
        using var document = JsonDocument.Parse(bytes.AsMemory());
        var root = document.RootElement;

        var receiptHead = String(root, "baseline_head_hash");
        var receiptGraph = String(root, "baseline_graph_root");
        if (receiptHead != baseline.HeadHash || receiptGraph != baseline.GraphRoot)
        {
            throw new FormatException(
                $"Revocation receipt is bound to another baseline (head={receiptHead == baseline.HeadHash}, graph={receiptGraph == baseline.GraphRoot}).");
        }

        if (!bytes.AsSpan().SequenceEqual(
                RevocationReceiptWriter.Write(baseline.HeadHash, baseline.GraphRoot, evidence).AsSpan()))
        {
            throw new FormatException("Revocation receipt bytes are noncanonical.");
        }

        ValidateClaim(baseline, evidence);
        return evidence;
    }

    private static bool SameClaim(RevocationEvidence trusted, RevocationEvidence candidate) =>
        (trusted, candidate) switch
        {
            (RevocationEvidence.KernelWitnessFailure left, RevocationEvidence.KernelWitnessFailure right) =>
                left.RootFrozenNodeId == right.RootFrozenNodeId
                && left.FailedStatementId == right.FailedStatementId,
            (RevocationEvidence.AllowedAxiomRetired left, RevocationEvidence.AllowedAxiomRetired right) =>
                left.RootFrozenNodeId == right.RootFrozenNodeId
                && left.AxiomName == right.AxiomName,
            (RevocationEvidence.FormalContradictionCertificate left,
                RevocationEvidence.FormalContradictionCertificate right) =>
                left.RootFrozenNodeId == right.RootFrozenNodeId
                && left.ContradictedStatementId == right.ContradictedStatementId,
            (RevocationEvidence.ContentAddressMismatch left, RevocationEvidence.ContentAddressMismatch right) =>
                left.RootFrozenNodeId == right.RootFrozenNodeId
                && left.ExpectedSha256 == right.ExpectedSha256
                && left.ActualSha256 == right.ActualSha256,
            _ => false,
        };

    private static RevocationEvidence ParseKernel(JsonElement value, FrozenNodeId root)
    {
        Fields(value, "baseline_graph_root", "baseline_head_hash", "evidence_type", "failed_statement_id",
            "kind", "root_frozen_node_id", "schema_version");
        var statement = String(value, "failed_statement_id");
        return FrozenHashSyntax.IsSha256(statement)
            ? new RevocationEvidence.KernelWitnessFailure(root, StatementId.Create(statement), string.Empty, string.Empty)
            : throw new FormatException("Typed kernel receipt has a malformed statement ID.");
    }

    private static RevocationEvidence ParseAxiom(JsonElement value, FrozenNodeId root)
    {
        Fields(value, "axiom_name", "baseline_graph_root", "baseline_head_hash", "evidence_type", "kind",
            "root_frozen_node_id", "schema_version");
        return new RevocationEvidence.AllowedAxiomRetired(
            root, String(value, "axiom_name"), string.Empty, string.Empty);
    }

    private static RevocationEvidence ParseContradiction(JsonElement value, FrozenNodeId root)
    {
        Fields(value, "baseline_graph_root", "baseline_head_hash", "contradicted_statement_id", "evidence_type",
            "kind", "root_frozen_node_id", "schema_version");
        var statement = String(value, "contradicted_statement_id");
        return FrozenHashSyntax.IsSha256(statement)
            ? new RevocationEvidence.FormalContradictionCertificate(
                root, StatementId.Create(statement), string.Empty, string.Empty)
            : throw new FormatException("Typed contradiction receipt has a malformed StatementId.");
    }

    private static RevocationEvidence ParseMismatch(JsonElement value, FrozenNodeId root)
    {
        Fields(value, "actual_sha256", "baseline_graph_root", "baseline_head_hash", "evidence_type",
            "expected_sha256", "kind", "root_frozen_node_id", "schema_version");
        return new RevocationEvidence.ContentAddressMismatch(
            root,
            String(value, "expected_sha256"),
            String(value, "actual_sha256"),
            string.Empty,
            string.Empty);
    }

    private static FrozenNodeId EvidenceRoot(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => item.RootFrozenNodeId,
        RevocationEvidence.AllowedAxiomRetired item => item.RootFrozenNodeId,
        RevocationEvidence.FormalContradictionCertificate item => item.RootFrozenNodeId,
        RevocationEvidence.ContentAddressMismatch item => item.RootFrozenNodeId,
        _ => throw new FormatException("Unknown revocation evidence variant."),
    };

    private static (string Oid, string Sha256) ReceiptAddress(RevocationEvidence evidence) => evidence switch
    {
        RevocationEvidence.KernelWitnessFailure item => (item.ReceiptBlobOid, item.ReceiptSha256),
        RevocationEvidence.AllowedAxiomRetired item => (item.ReceiptBlobOid, item.ReceiptSha256),
        RevocationEvidence.FormalContradictionCertificate item => (item.ReceiptBlobOid, item.ReceiptSha256),
        RevocationEvidence.ContentAddressMismatch item => (item.ReceiptBlobOid, item.ReceiptSha256),
        _ => throw new FormatException("Unknown revocation evidence variant."),
    };

    private static RevocationEvidence WithReceiptAddress(
        RevocationEvidence evidence,
        string oid,
        string sha256) => evidence switch
        {
            RevocationEvidence.KernelWitnessFailure item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha256,
            },
            RevocationEvidence.AllowedAxiomRetired item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha256,
            },
            RevocationEvidence.FormalContradictionCertificate item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha256,
            },
            RevocationEvidence.ContentAddressMismatch item => item with
            {
                ReceiptBlobOid = oid,
                ReceiptSha256 = sha256,
            },
            _ => throw new FormatException("Unknown revocation evidence variant."),
        };

    private static FrozenNodeId FrozenNode(string value) =>
        FrozenHashSyntax.IsSha256(value)
            ? FrozenNodeId.Create(value)
            : throw new FormatException("Typed receipt root is malformed.");

    private static void Fields(JsonElement value, params string[] expected)
    {
        if (value.ValueKind != JsonValueKind.Object
            || !value.EnumerateObject().Select(static property => property.Name)
                .Order(StringComparer.Ordinal)
                .SequenceEqual(expected.Order(StringComparer.Ordinal), StringComparer.Ordinal))
        {
            throw new FormatException("Typed revocation receipt has unknown, duplicate, or missing fields.");
        }
    }

    private static string String(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property) && property.ValueKind == JsonValueKind.String
            ? property.GetString() ?? throw new FormatException($"{name} is null.")
            : throw new FormatException($"{name} must be a string.");

    private static int Integer(JsonElement value, string name) =>
        value.TryGetProperty(name, out var property)
        && property.ValueKind == JsonValueKind.Number
        && property.TryGetInt32(out var result)
            ? result
            : throw new FormatException($"{name} must be an integer.");

    private sealed record TrustedReceipt(
        ImmutableArray<byte> Bytes,
        string Sha256,
        RevocationEvidence Evidence);
}

[Union(EnableImplicitConversions = false)]
public partial record RevocationReceiptStoreOutcome
{
    public partial record Accepted
    {
        internal Accepted(TrustedRevocationReceiptStore capability) =>
            Capability = capability ?? throw new ArgumentNullException(nameof(capability));

        public TrustedRevocationReceiptStore Capability { get; }
    }

    public partial record Rejected(string Message);
}
