using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    public enum ReplayConfirmationTruthTableStatus
    {
        ResidualOpen,
        PartialClosed,
        AbsorbedClosed,
    }

    public enum ReplayConfirmationTruthTableAlignment
    {
        Seen,
        Rejected,
    }

    [Theory]
    [InlineData(
        "acknowledged-acknowledged",
        true,
        true,
        ReplayConfirmationTruthTableStatus.AbsorbedClosed,
        ReplayConfirmationTruthTableStatus.PartialClosed,
        ReplayConfirmationTruthTableAlignment.Seen)]
    [InlineData(
        "unacknowledged-unacknowledged-equal",
        false,
        false,
        ReplayConfirmationTruthTableStatus.PartialClosed,
        ReplayConfirmationTruthTableStatus.PartialClosed,
        ReplayConfirmationTruthTableAlignment.Seen)]
    [InlineData(
        "unacknowledged-unacknowledged-unequal",
        false,
        false,
        ReplayConfirmationTruthTableStatus.AbsorbedClosed,
        ReplayConfirmationTruthTableStatus.PartialClosed,
        ReplayConfirmationTruthTableAlignment.Rejected)]
    [InlineData(
        "acknowledged-unacknowledged-structural-positive",
        true,
        false,
        ReplayConfirmationTruthTableStatus.AbsorbedClosed,
        ReplayConfirmationTruthTableStatus.ResidualOpen,
        ReplayConfirmationTruthTableAlignment.Seen)]
    [InlineData(
        "acknowledged-unacknowledged-nonstructural-negative",
        true,
        false,
        ReplayConfirmationTruthTableStatus.AbsorbedClosed,
        ReplayConfirmationTruthTableStatus.PartialClosed,
        ReplayConfirmationTruthTableAlignment.Rejected)]
    [InlineData(
        "unacknowledged-acknowledged-structural-positive",
        false,
        true,
        ReplayConfirmationTruthTableStatus.ResidualOpen,
        ReplayConfirmationTruthTableStatus.AbsorbedClosed,
        ReplayConfirmationTruthTableAlignment.Seen)]
    [InlineData(
        "unacknowledged-acknowledged-nonstructural-negative",
        false,
        true,
        ReplayConfirmationTruthTableStatus.PartialClosed,
        ReplayConfirmationTruthTableStatus.AbsorbedClosed,
        ReplayConfirmationTruthTableAlignment.Rejected)]
    public void AcknowledgedStaleFourArmTruthTableControlsReplayConfirmationAlignment(
        string arm,
        bool candidateAcknowledged,
        bool baselineAcknowledged,
        ReplayConfirmationTruthTableStatus candidateStatus,
        ReplayConfirmationTruthTableStatus baselineStatus,
        ReplayConfirmationTruthTableAlignment expectedAlignment)
    {
        var historicalBytes = Encoding.UTF8.GetBytes("historical receipt\n");
        var currentBytes = Encoding.UTF8.GetBytes("current receipt\n");
        var historical = Atom("historical", historicalBytes);
        var current = Atom("current", currentBytes);
        var capture = DigestionCasStore.Capture(historical.RawBytes.AsSpan());
        var atomId = AtomId(historical);
        var entry = Entry("historical", historical);
        IReadOnlyList<string> candidateAcknowledgedStale =
            candidateAcknowledged ? [atomId] : [];
        IReadOnlyList<string> baselineAcknowledgedStale =
            baselineAcknowledged ? [atomId] : [];
        var candidate = Ledger(
            candidateAcknowledgedStale,
            entry with
            {
                ProjectedStatus = TruthTableStatus(candidateStatus),
            });
        var baseline = Ledger(
            baselineAcknowledgedStale,
            entry with
            {
                ProjectedStatus = TruthTableStatus(baselineStatus),
            });

        var result = DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(current));

        Assert.NotEmpty(arm);
        Assert.Empty(result.Findings);
        var actualAlignment = result.AlignmentFor(atomId);
        if (expectedAlignment == ReplayConfirmationTruthTableAlignment.Seen)
        {
            Assert.Equal(DigestionReceiptAlignment.Seen, actualAlignment);
        }
        else
        {
            Assert.Equal(DigestionReceiptAlignment.Rejected, actualAlignment);
        }
    }

    private static DigestionStatus TruthTableStatus(
        ReplayConfirmationTruthTableStatus status) => status switch
        {
            ReplayConfirmationTruthTableStatus.ResidualOpen => new DigestionStatus(
                DigestionMigrationState.Residual,
                DigestionTruthState.Open),
            ReplayConfirmationTruthTableStatus.PartialClosed => new DigestionStatus(
                DigestionMigrationState.Partial,
                DigestionTruthState.Closed),
            ReplayConfirmationTruthTableStatus.AbsorbedClosed => new DigestionStatus(
                DigestionMigrationState.Absorbed,
                DigestionTruthState.Closed),
            _ => throw new ArgumentOutOfRangeException(nameof(status)),
        };
}
