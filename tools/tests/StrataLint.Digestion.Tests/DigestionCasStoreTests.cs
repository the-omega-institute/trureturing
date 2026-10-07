using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Digestion.Tests;

public sealed class DigestionCasStoreTests
{
    [Fact]
    public void StatusEvaluationDoesNotScanForOrphanCasObjects()
    {
        var referenced = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("referenced atom\n"));
        var orphan = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("orphan atom\n"));
        var document = Ledger(referenced.Reference);
        var snapshot = Snapshot(
            new RawRepositoryEntry(referenced.RelativePath, referenced.Bytes),
            new RawRepositoryEntry(orphan.RelativePath, orphan.Bytes));

        var added = DigestionCasStore.EvaluateLedgerReferences(
            document,
            snapshot,
            RawChangeSet.Create([orphan.RelativePath]));
        var wholeLedger = DigestionCasStore.EvaluateLedgerReferences(document, snapshot);

        Assert.Empty(added.Findings);
        Assert.Empty(wholeLedger.Findings);
    }

    [Fact]
    public void CasRefMustEqualTheReceiptRawFingerprint()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("bound atom\n"));
        var other = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("other atom\n"));
        var document = Ledger(captured.Reference, other.Reference);
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, captured.Bytes));

        var evaluation = DigestionCasStore.EvaluateLedgerReferences(document, snapshot);

        Assert.Contains(
            $"entry synthetic-atom cas_ref {captured.Reference} differs from raw fingerprint {other.Reference}",
            evaluation.Findings);
    }

    [Fact]
    public void StatusEvaluationDoesNotRehashAReferencedBlob()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("expected atom\n"));
        var tampered = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("tampered atom\n"));
        var document = Ledger(captured.Reference);
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, tampered.Bytes));

        var evaluation = DigestionCasStore.EvaluateLedgerReferences(document, snapshot);

        Assert.Empty(evaluation.Findings);
    }

    [Fact]
    public void CandidateDeltaDoesNotTriggerCasRehashing()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("expected atom\n"));
        var tampered = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("tampered atom\n"));
        var document = Ledger(captured.Reference);
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, tampered.Bytes));

        var unrelated = DigestionCasStore.EvaluateLedgerReferences(
            document,
            snapshot,
            RawChangeSet.Create(["notes/unrelated.txt"]));
        var changed = DigestionCasStore.EvaluateLedgerReferences(
            document,
            snapshot,
            RawChangeSet.Create([captured.RelativePath]));

        Assert.Empty(unrelated.Findings);
        Assert.Empty(changed.Findings);
    }

    [Fact]
    public void StatusEvaluationDoesNotRejectAnUnloadedReferencedBlob()
    {
        var captured = DigestionCasStore.Capture(Encoding.UTF8.GetBytes("missing atom\n"));
        var document = Ledger(captured.Reference);

        var evaluation = DigestionCasStore.EvaluateLedgerReferences(document, Snapshot());

        Assert.Empty(evaluation.Findings);
    }

    [Fact]
    public void CaptureRoundTripsExactAtomBytes()
    {
        var bytes = ImmutableArray.Create<byte>(0xff, 0x00, 0xfe, (byte)'\n');
        var captured = DigestionCasStore.Capture(bytes.AsSpan());
        var document = Ledger(captured.Reference);
        var snapshot = Snapshot(new RawRepositoryEntry(captured.RelativePath, captured.Bytes));

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
                        new DigestionReceipts([], [], null),
                        new DigestionStatus(
                            DigestionMigrationState.Residual,
                            DigestionTruthState.Open),
                        casRef),
                ]),
        ],
        []);
}
