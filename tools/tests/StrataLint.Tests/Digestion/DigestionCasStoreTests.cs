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
        var document = Ledger(referenced.Reference);
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
        var document = Ledger(captured.Reference, other.Reference);
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
        var document = Ledger(captured.Reference);
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, tampered.Bytes));

        var evaluation = DigestionCasStore.Evaluate(document, snapshot);

        Assert.Contains(
            $"entry synthetic-atom CAS blob hash mismatch: {captured.RelativePath} "
            + $"declares {captured.Reference} but contains {tampered.Reference}",
            evaluation.Findings);
    }

    [Fact]
    public void CandidateDeltaRehashesOnlyChangedCasObjects()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("expected atom\n"));
        var tampered = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("tampered atom\n"));
        var document = Ledger(captured.Reference);
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, tampered.Bytes));

        var unrelated = DigestionCasStore.Evaluate(
            document,
            snapshot,
            RawChangeSet.Create(["notes/unrelated.txt"]));
        var changed = DigestionCasStore.Evaluate(
            document,
            snapshot,
            RawChangeSet.Create([captured.RelativePath]));

        Assert.Equal(0, unrelated.RehashedObjectCount);
        Assert.Empty(unrelated.Findings);
        Assert.Equal(1, changed.RehashedObjectCount);
        Assert.Contains(changed.Findings, finding => finding.Contains(
            "CAS blob hash mismatch",
            StringComparison.Ordinal));
    }

    [Fact]
    public void MissingReferencedBlobIsRejected()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("missing atom\n"));
        var document = Ledger(captured.Reference);

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
        var document = Ledger(captured.Reference);
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

    private static BackfillInventoryDocument Ledger(string casRef, string? rawSha256 = null) =>
        BackfillInventoryDocument.Create(
        [
            new DigestionLedgerSource(
                "synthetic-source",
                "docs/source.md",
                AtomizerRegistry.NoAtomizerId,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
                [
                    new DigestionLedgerEntry(
                        "synthetic-source",
                        "docs/source.md",
                        AtomizerRegistry.NoAtomizerId,
                        "synthetic-atom",
                        new DigestionFingerprints(rawSha256 ?? casRef, casRef),
                        [],
                        new DigestionReceipts([], [], [], [], null),
                        new DigestionStatus(
                            DigestionMigrationState.Residual,
                            DigestionTruthState.Open),
                        casRef),
                ]),
        ],
        []);
}
