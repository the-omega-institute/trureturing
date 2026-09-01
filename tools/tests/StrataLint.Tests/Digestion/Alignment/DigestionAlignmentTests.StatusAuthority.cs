using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void ChangedStatusWithCanonicalDirectoryMoveCannotInheritBaselineReceipt()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var newBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var entry = Entry("old-receipt", oldAtom);
        var baseline = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        });
        var candidateEntry = entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };
        var candidate = Ledger([], candidateEntry);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(
                newBytes,
                [oldCapture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/partial-open/{AtomId(oldAtom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            baseline,
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(oldAtom)));
        Assert.Single(result.Residual);
    }

    [Fact]
    public void IngestStatusAuthorityRejectionSurvivesRawFingerprintMatch()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。unchanged。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(sourceBytes, DigestionTestSupport.Rules).Claims);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };

        var result = DigestionLedgerAligner.Evaluate(
            Ledger([], candidateEntry),
            Snapshot(
                sourceBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/partial-open/{AtomId(atom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            Ledger([], baselineEntry),
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(atom)));
        Assert.Null(result.AtomFor(AtomId(atom)));
    }

    [Fact]
    public void IngestStatusAuthorityRejectionSurvivesNormalizedFingerprintMatch()
    {
        var baselineBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。unchanged。\n");
        var candidateBytes = Encoding.UTF8.GetBytes("# GICT\r\n\r\n**定理 1.1(A)**。unchanged。\r\n");
        var baselineAtom = Assert.Single(GictAtomizer.Atomize(
            baselineBytes,
            DigestionTestSupport.Rules).Claims);
        var candidateAtom = Assert.Single(GictAtomizer.Atomize(
            candidateBytes,
            DigestionTestSupport.Rules).Claims);
        Assert.NotEqual(baselineAtom.Fingerprints.RawSha256, candidateAtom.Fingerprints.RawSha256);
        Assert.Equal(
            baselineAtom.Fingerprints.NormalizedSha256,
            candidateAtom.Fingerprints.NormalizedSha256);

        var capture = DigestionCasStore.Capture(baselineAtom.RawBytes.AsSpan());
        var baselineEntry = Entry("baseline", baselineAtom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };

        var result = DigestionLedgerAligner.Evaluate(
            Ledger([], candidateEntry),
            Snapshot(
                candidateBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/partial-open/{AtomId(baselineAtom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            Ledger([], baselineEntry),
            DigestionAlignmentMode.Ingest);

        Assert.Empty(result.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(AtomId(baselineAtom)));
        Assert.Null(result.AtomFor(AtomId(baselineAtom)));
    }

    [Fact]
    public void CanonicalStatusDirectoryMoveWithoutReceiptFailsClosedInAdmission()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("opaque status move source\n");
        var atomBytes = Encoding.UTF8.GetBytes("settled atom\n");
        var atom = new DigestionAtom(
            0,
            atomBytes.Length,
            ImmutableArray.CreateRange(atomBytes),
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var atomId = AtomId(atom);
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        };
        var baseline = WithAtomizer(
            Ledger([], baselineEntry),
            AtomizerRegistry.NoAtomizerId);
        var candidate = WithAtomizer(
            Ledger([], candidateEntry),
            AtomizerRegistry.NoAtomizerId);
        var baselinePath = $"Meta/Digestion/backfill/source/absorbed-open/{atomId}.yaml";
        var candidatePath = $"Meta/Digestion/backfill/source/partial-open/{atomId}.yaml";
        var changes = RawChangeSet.CreateWithKinds(
        [
            (baselinePath, RawChangeKind.Deleted),
            (candidatePath, RawChangeKind.Added),
        ]);

        var evaluation = DigestionStatusEvaluator.Evaluate(
            DigestionEvaluationScope.ChangedSet,
            candidate,
            Snapshot(
                sourceBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        candidatePath,
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            DigestionTestSupport.AcceptedLean(Array.Empty<string>()),
            baselineDocument: baseline,
            changes: changes);
        var evaluated = Assert.Single(evaluation.Entries);

        Assert.Equal(DigestionReceiptAlignment.Seen, evaluated.Alignment);
        Assert.Equal(
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            evaluated.DerivedStatus);
        Assert.Contains(
            $"entry {atomId} handwritten status partial-open differs from derived residual-open",
            evaluation.Findings);
    }

    [Fact]
    public void SettledReceiptSurvivesAcknowledgedStaleSourceViewSplit()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("opaque settled source\n");
        var atomBytes = Encoding.UTF8.GetBytes("settled atom\n");
        var atom = new DigestionAtom(
            0,
            atomBytes.Length,
            ImmutableArray.CreateRange(atomBytes),
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var atomId = AtomId(atom);
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
        };
        var baseline = WithAtomizer(
            Ledger([atomId], baselineEntry),
            AtomizerRegistry.NoAtomizerId);
        var candidate = WithAtomizer(
            Ledger([], candidateEntry),
            AtomizerRegistry.NoAtomizerId);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(sourceBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(atomId));
    }

    [Fact]
    public void ProjectedStatusDirectoryMoveSurvivesBaselineIdentity()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("status directory move source\n");
        var atomBytes = Encoding.UTF8.GetBytes("settled atom\n");
        var atom = new DigestionAtom(
            0,
            atomBytes.Length,
            ImmutableArray.CreateRange(atomBytes),
            DigestionFingerprint.Compute(atomBytes.AsSpan()),
            []);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var baselineEntry = Entry("baseline", atom) with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
        };
        var candidateEntry = baselineEntry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
        };
        var baseline = WithAtomizer(
            Ledger([], baselineEntry),
            AtomizerRegistry.NoAtomizerId);
        var candidate = WithAtomizer(
            Ledger([], candidateEntry),
            AtomizerRegistry.NoAtomizerId);

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(
                sourceBytes,
                [capture],
                extraEntries:
                [
                    new RawRepositoryEntry(
                        $"Meta/Digestion/backfill/source/absorbed-closed/{AtomId(atom)}.yaml",
                        BackfillInventoryWriter.WriteAtom(candidateEntry)),
                ]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(atom)));
    }
}
