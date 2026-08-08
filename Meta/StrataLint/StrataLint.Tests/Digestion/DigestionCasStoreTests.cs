using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionCasStoreTests
{
    [Fact]
    public void BaselineCasObjectsCannotBeDeletedOrRewritten()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("frozen atom\n"));
        var baseline = Snapshot(new RawRepositoryEntry(captured.RelativePath, captured.Bytes));
        var rewritten = Snapshot(new RawRepositoryEntry(
            captured.RelativePath,
            ImmutableArray.CreateRange(Encoding.UTF8.GetBytes("rewritten atom\n"))));

        var deletedFindings = DigestionCasStore.ValidateAppendOnly(Snapshot(), baseline);
        var rewrittenFindings = DigestionCasStore.ValidateAppendOnly(rewritten, baseline);

        Assert.Contains($"baseline CAS blob was deleted: {captured.RelativePath}", deletedFindings);
        Assert.Contains($"baseline CAS blob was rewritten: {captured.RelativePath}", rewrittenFindings);
    }

    [Fact]
    public void UnreferencedBlobIsRejectedAsAnOrphan()
    {
        var referenced = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("referenced atom\n"));
        var orphan = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("orphan atom\n"));
        var document = BackfillInventoryLoader.Load(Ledger(referenced.Reference));
        var snapshot = Snapshot(
            new RawRepositoryEntry(referenced.RelativePath, referenced.Bytes),
            new RawRepositoryEntry(orphan.RelativePath, orphan.Bytes));

        var evaluation = DigestionCasStore.Evaluate(document, snapshot);

        Assert.Contains($"orphan CAS blob: {orphan.RelativePath}", evaluation.Findings);
    }

    [Fact]
    public void CasRefMustEqualTheReceiptRawFingerprint()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("bound atom\n"));
        var other = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("other atom\n"));
        var document = BackfillInventoryLoader.Load(Ledger(captured.Reference, other.Reference));
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, captured.Bytes));

        var evaluation = DigestionCasStore.Evaluate(document, snapshot);

        Assert.Contains(
            $"entry synthetic-atom cas_ref {captured.Reference} differs from raw fingerprint {other.Reference}",
            evaluation.Findings);
    }

    [Fact]
    public void HashMismatchedBlobIsRejected()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("expected atom\n"));
        var tampered = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("tampered atom\n"));
        var document = BackfillInventoryLoader.Load(Ledger(captured.Reference));
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, tampered.Bytes));

        var evaluation = DigestionCasStore.Evaluate(document, snapshot);

        Assert.Contains(
            $"entry synthetic-atom CAS blob hash mismatch: {captured.RelativePath} "
            + $"declares {captured.Reference} but contains {tampered.Reference}",
            evaluation.Findings);
    }

    [Fact]
    public void MissingReferencedBlobIsRejected()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("missing atom\n"));
        var document = BackfillInventoryLoader.Load(Ledger(captured.Reference));

        var evaluation = DigestionCasStore.Evaluate(document, Snapshot());

        Assert.Contains(
            $"entry synthetic-atom CAS blob is missing: {captured.RelativePath}",
            evaluation.Findings);
    }

    [Fact]
    public void CaptureRoundTripsExactAtomBytes()
    {
        var bytes = ImmutableArray.Create<byte>(0xff, 0x00, 0xfe, (byte)'\n');
        var captured = DigestionCasStore.Capture(bytes.AsSpan());
        var document = BackfillInventoryLoader.Load(Ledger(captured.Reference));
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, captured.Bytes));

        var evaluation = DigestionCasStore.Evaluate(document, snapshot);

        Assert.Empty(evaluation.Findings);
        Assert.StartsWith("sha256:", captured.Reference, StringComparison.Ordinal);
        Assert.Equal(
            DigestionCasStore.RootPath + captured.Reference["sha256:".Length..],
            captured.RelativePath);
        Assert.True(snapshot.TryGetFile(captured.RelativePath, out var stored));
        Assert.Equal(bytes.ToArray(), stored.RawBytes.ToArray());
    }

    private static RepositorySnapshot Snapshot(params RawRepositoryEntry[] entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;

    private static string Ledger(string casRef, string? rawSha256 = null) => $$"""
        schema_version: 3
        ledger: theory-digestion-v1
        sources:
          - source_id: synthetic-source
            path: docs/source.md
            atomizer: {{AtomizerRegistry.NoAtomizerId}}
            entries:
              - atom_id: synthetic-atom
                ast_path: theorem/1.1
                fingerprints:
                  raw_sha256: {{rawSha256 ?? casRef}}
                  normalized_sha256: {{casRef}}
                cas_ref: {{casRef}}
                coverage_gids: []
                receipts:
                  coverage: []
                  scribe: []
                  unresolved_subitems: []
                status:
                  migration: residual
                  truth: open
        ticket_index: []
        """;
}
