using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void ReplayRejectionRequiresCasValidReceipt()
    {
        Assert.True(RequiresReplayRejection());
        Assert.False(RequiresReplayRejection(casValid: false));
    }

    [Fact]
    public void ReplayRejectionRequiresSeenAlignment()
    {
        Assert.True(RequiresReplayRejection());
        Assert.False(RequiresReplayRejection(
            alignment: DigestionReceiptAlignment.Rejected));
    }

    [Fact]
    public void ReplayRejectionRequiresNewInheritanceObligation()
    {
        Assert.True(RequiresReplayRejection());
        Assert.False(RequiresReplayRejection(confirmationRequired: false));
    }

    [Fact]
    public void ReplayRejectionExemptsContentWideReceipt()
    {
        Assert.True(RequiresReplayRejection());
        Assert.False(RequiresReplayRejection(contentWide: true));
    }

    [Fact]
    public void ReplayRejectionExemptsClauseChainChildReceipt()
    {
        Assert.True(RequiresReplayRejection());
        Assert.False(RequiresReplayRejection(clauseChainChild: true));
    }

    [Fact]
    public void ReplayRejectionRequiresMissingReplayedFingerprint()
    {
        Assert.True(RequiresReplayRejection());
        Assert.False(RequiresReplayRejection(fingerprintConfirmed: true));
    }

    [Fact]
    public void AdmissionChangedStatusCannotInheritBaselineReceipt()
    {
        var oldBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。rewritten。\n");
        var oldAtom = Assert.Single(GictAtomizer.Atomize(oldBytes, DigestionTestSupport.Rules).Claims);
        var oldCapture = DigestionCasStore.Capture(oldAtom.RawBytes.AsSpan());
        var entry = Entry("old-receipt", oldAtom);
        var baseline = WithGenreCheck(
            Ledger([], entry with
            {
                ProjectedStatus = new DigestionStatus(
                    DigestionMigrationState.Absorbed,
                    DigestionTruthState.Open),
            }),
            GenreRegistryCheck.Collected([]));
        var candidate = WithGenreCheck(
            Ledger([], entry with
            {
                ProjectedStatus = new DigestionStatus(
                    DigestionMigrationState.Partial,
                    DigestionTruthState.Open),
            }),
            GenreRegistryCheck.Collected([]));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [oldCapture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(oldAtom)));
        Assert.Single(result.Residual);
    }

    [Fact]
    public void AdmissionKeepsUnchangedInheritedReceiptWithoutReplayingSource()
    {
        var sourceBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。unchanged。\n");
        var atom = Assert.Single(GictAtomizer.Atomize(
            sourceBytes,
            DigestionTestSupport.Rules).Claims);
        var capture = DigestionCasStore.Capture(atom.RawBytes.AsSpan());
        var ledger = WithGenreCheck(
            Ledger([], Entry("unchanged", atom)),
            GenreRegistryCheck.Collected([]));
        var snapshot = Snapshot(sourceBytes, [capture]);
        var calls = 0;

        var result = DigestionLedgerAligner.Evaluate(
            ledger,
            snapshot,
            ledger,
            DigestionAlignmentMode.Admission,
            _ => (bytes, rules) =>
            {
                calls++;
                return GictAtomizer.Atomize(bytes, rules);
            },
            baselineSnapshot: snapshot);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(atom)));
        Assert.Equal(0, calls);
    }

    [Fact]
    public void AdmissionConfirmsHistoricalFineReceiptWithinReplayedClaim()
    {
        var fineBytes = Encoding.UTF8.GetBytes("historical fine receipt\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "current claim prefix\nhistorical fine receipt\ncurrent claim suffix\n");
        var fine = Atom("fine", fineBytes);
        var current = Atom("current", currentBytes);
        var capture = DigestionCasStore.Capture(fine.RawBytes.AsSpan());
        var entry = Entry("fine", fine);
        var baseline = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        });
        var candidate = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        });

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(current));

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(fine)));
        Assert.Single(result.Residual);
    }

    [Fact]
    public void AdmissionConfirmsHistoricalFineReceiptAcrossInsertedReplayBlock()
    {
        var fineBytes = Encoding.UTF8.GetBytes(
            "## Theorem 1\n\nconclusion\n\n[\nformula\n]\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "## Theorem 1\n\nnew assumption\n\nconclusion\n\n[\nformula\n]\n");
        var fine = Atom("fine", fineBytes);
        var current = Atom("current", currentBytes);
        var capture = DigestionCasStore.Capture(fine.RawBytes.AsSpan());
        var entry = Entry("fine", fine);
        var baseline = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        });
        var candidate = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        });

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(current));

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(fine)));
        Assert.Single(result.Residual);
    }

    [Fact]
    public void AdmissionRejectsHistoricalFineReceiptWhenReplayInterruptsItsBody()
    {
        var fineBytes = Encoding.UTF8.GetBytes(
            "## Theorem 1\n\nconclusion\n\n[\nformula\n]\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "## Theorem 1\n\nnew assumption\n\nconclusion\n\nnew qualification\n\n[\nformula\n]\n");
        var fine = Atom("fine", fineBytes);
        var current = Atom("current", currentBytes);
        var capture = DigestionCasStore.Capture(fine.RawBytes.AsSpan());
        var entry = Entry("fine", fine);
        var baseline = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Open),
        });
        var candidate = Ledger([], entry with
        {
            ProjectedStatus = new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Open),
        });

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(current));

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(fine)));
        Assert.Single(result.Residual);
    }

    [Fact]
    public void AdmissionZeroClaimReplayRejectsNewlyInheritedFineReceipt()
    {
        var baselineBytes = Encoding.UTF8.GetBytes("# GICT\n\n**定理 1.1(A)**。old。\n");
        var currentBytes = Encoding.UTF8.GetBytes("unrecognized current source\n");
        var fine = Assert.Single(GictAtomizer.Atomize(
            baselineBytes,
            DigestionTestSupport.Rules).Claims);
        var coarseBytes = ImmutableArray.CreateRange(currentBytes);
        var coarse = new DigestionAtom(
            0,
            coarseBytes.Length,
            coarseBytes,
            DigestionFingerprint.ComputeOpaque(coarseBytes.AsSpan()),
            []);
        var fineCapture = DigestionCasStore.Capture(fine.RawBytes.AsSpan());
        var coarseCapture = DigestionCasStore.Capture(coarse.RawBytes.AsSpan());
        var fineEntry = Entry("fine", fine);
        var baseline = WithGenreCheck(
            Ledger([], fineEntry with
            {
                ProjectedStatus = new DigestionStatus(
                    DigestionMigrationState.Absorbed,
                    DigestionTruthState.Open),
            }),
            GenreRegistryCheck.Collected([]));
        var candidate = WithGenreCheck(
            Ledger(
                [],
                fineEntry with
                {
                    ProjectedStatus = new DigestionStatus(
                        DigestionMigrationState.Partial,
                        DigestionTruthState.Open),
                },
                Entry("coarse", coarse)),
            GenreRegistryCheck.Collected([]));

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [fineCapture, coarseCapture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Empty(result.Findings);
        Assert.Equal(DigestionReceiptAlignment.Rejected, result.AlignmentFor(AtomId(fine)));
        Assert.Equal(DigestionReceiptAlignment.Seen, result.AlignmentFor(AtomId(coarse)));
        Assert.Empty(result.Residual);
    }

    private static bool RequiresReplayRejection(
        bool casValid = true,
        DigestionReceiptAlignment alignment = DigestionReceiptAlignment.Seen,
        bool confirmationRequired = true,
        bool contentWide = false,
        bool clauseChainChild = false,
        bool fingerprintConfirmed = false) =>
        DigestionLedgerAligner.RequiresReplayRejection(
            casValid,
            alignment,
            confirmationRequired,
            contentWide,
            clauseChainChild,
            fingerprintConfirmed);
}
