using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Engine.Tests;

public sealed class DigestionReceiptIntegrityPredicateTests
{
    [Fact]
    public void EmptyEvaluationHasNoReceiptIntegrityFailure()
    {
        Assert.False(new DigestionLedgerEvaluation([], []).HasReceiptIntegrityFailure);
    }

    [Fact]
    public void FindingIsAReceiptIntegrityFailure()
    {
        Assert.True(new DigestionLedgerEvaluation([], ["finding"]).HasReceiptIntegrityFailure);
    }

    [Fact]
    public void NonFatalGapIsNotAReceiptIntegrityFailure()
    {
        Assert.False(EvaluationWithGap(DigestionGapSeverity.NonFatal).HasReceiptIntegrityFailure);
    }

    [Fact]
    public void ReceiptIntegrityGapIsAReceiptIntegrityFailure()
    {
        Assert.True(EvaluationWithGap(
            DigestionGapSeverity.ReceiptIntegrityFailure).HasReceiptIntegrityFailure);
    }

    private static DigestionLedgerEvaluation EvaluationWithGap(DigestionGapSeverity severity)
    {
        var status = new DigestionStatus(
            DigestionMigrationState.Partial,
            DigestionTruthState.Closed);
        var entry = new DigestionLedgerEntry(
            "source",
            "docs/source.md",
            "none",
            "atom",
            "manual/atom",
            null,
            new DigestionFingerprints("sha256:synthetic", "sha256:synthetic"),
            [],
            new DigestionReceipts([], [], [], [], null),
            status,
            "sha256:synthetic");
        var evaluated = new DigestionEntryEvaluation(
            entry,
            DigestionReceiptAlignment.Seen,
            status,
            false,
            ImmutableArray.Create(new DigestionGap("gap", "detail", severity)));
        return new DigestionLedgerEvaluation([evaluated], []);
    }
}
