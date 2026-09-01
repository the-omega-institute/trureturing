using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class DigestionAlignmentTests
{
    [Fact]
    public void AdmissionConflictedSourceStillRejectsUnconfirmedInheritedReceipt()
    {
        var historicalBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**Theorem 1.1(A)**. historical.\n");
        var conflictedBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n<<<<<<< HEAD\n**Theorem 1.1(A)**. rewritten.\n"
            + "=======\n**Theorem 1.1(A)**. competing.\n>>>>>>> branch\n");
        var historical = Assert.Single(GictAtomizer.Atomize(
            historicalBytes,
            DigestionTestSupport.Rules).Claims);
        var capture = DigestionCasStore.Capture(historical.RawBytes.AsSpan());
        var entry = Entry("historical", historical);
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
            Snapshot(conflictedBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission);

        Assert.Contains(result.Findings, static finding => finding.Contains(
            "INGEST-CONFLICT-MARKER-001",
            StringComparison.Ordinal));
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(AtomId(historical)));
    }

    [Fact]
    public void ProjectionChangedStatusKeepsInheritedReceiptWithoutReplayConfirmation()
    {
        var historicalBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**Theorem 1.1(A)**. historical.\n");
        var currentBytes = Encoding.UTF8.GetBytes(
            "# GICT\n\n**Theorem 1.1(A)**. rewritten.\n");
        var historical = Assert.Single(GictAtomizer.Atomize(
            historicalBytes,
            DigestionTestSupport.Rules).Claims);
        var capture = DigestionCasStore.Capture(historical.RawBytes.AsSpan());
        var entry = Entry("historical", historical);
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
            DigestionAlignmentMode.Projection);

        Assert.Empty(result.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(AtomId(historical)));
    }

    [Fact]
    public void AdmissionUnregisteredAtomizerExitRejectsUnconfirmedInheritedReceipt()
    {
        var fixture = ReplayExitFixture.Create(AtomizerRegistry.NoAtomizerId);

        var result = fixture.Evaluate(Snapshot(fixture.CurrentBytes, [fixture.Capture]));

        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(fixture.AtomId));
    }

    [Fact]
    public void AdmissionMissingSourceExitRejectsUnconfirmedInheritedReceipt()
    {
        var fixture = ReplayExitFixture.Create();
        var snapshot = DecodeSnapshot(
            new RawRepositoryEntry(
                TheoryAtomizerDataLoader.DataPath,
                ImmutableArray.CreateRange(DigestionTestSupport.RulesBytes)),
            new RawRepositoryEntry(fixture.Capture.RelativePath, fixture.Capture.Bytes));

        var result = fixture.Evaluate(snapshot);

        Assert.Contains(result.Findings, static finding => finding.Contains(
            "source path is dangling",
            StringComparison.Ordinal));
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(fixture.AtomId));
    }

    [Fact]
    public void AdmissionMissingAtomizerRulesExitRejectsUnconfirmedInheritedReceipt()
    {
        var fixture = ReplayExitFixture.Create();
        var snapshot = DecodeSnapshot(
            new RawRepositoryEntry(
                "docs/source.md",
                ImmutableArray.CreateRange(fixture.CurrentBytes)),
            new RawRepositoryEntry(fixture.Capture.RelativePath, fixture.Capture.Bytes));

        var result = fixture.Evaluate(snapshot);

        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(fixture.AtomId));
    }

    [Fact]
    public void AdmissionAtomizerFailureExitRejectsUnconfirmedInheritedReceipt()
    {
        var fixture = ReplayExitFixture.Create();

        var result = fixture.Evaluate(
            Snapshot(fixture.CurrentBytes, [fixture.Capture]),
            _ => (_, _) => throw new DecoderFallbackException("invalid source encoding"));

        Assert.Contains(result.Findings, static finding => finding.Contains(
            "atomization failed",
            StringComparison.Ordinal));
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(fixture.AtomId));
    }

    [Fact]
    public void AdmissionAtomizerIntegrityExitRejectsUnconfirmedInheritedReceipt()
    {
        var fixture = ReplayExitFixture.Create();
        var current = Atom("current", fixture.CurrentBytes);

        var result = fixture.Evaluate(
            Snapshot(fixture.CurrentBytes, [fixture.Capture]),
            _ => (_, _) => new AtomizedTheoryDocument(
                [current],
                [new DigestionSlice(true, [])],
                GenreRegistryCheck.NoGenreRegistry));

        Assert.Contains(result.Findings, static finding => finding.Contains(
            "atomizer integrity failed",
            StringComparison.Ordinal));
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(fixture.AtomId));
    }

    [Fact]
    public void Review3996AcceptsCompleteHistoricalBlocksBeforeAppendedBlock()
    {
        const string historical = "## Theorem 1\n\nconclusion\n\n[\nformula\n]\n";
        const string current = "## Theorem 1\n \nconclusion\n \n[\nformula\n]\n\nappended block\n";

        var result = EvaluateHistoricalBlockReplay(historical, current);

        Assert.Empty(result.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Seen,
            result.AlignmentFor(OnlyAtomId(result)));
    }

    [Fact]
    public void Review3996RejectsHistoricalBodyMovedUnderAnotherHeading()
    {
        const string historical = "## Theorem 1\n\nconclusion\n\n[\nformula\n]\n";
        const string current =
            "## Theorem 1\n\n## Theorem 2\n\nconclusion\n\n[\nformula\n]\n";

        var result = EvaluateHistoricalBlockReplay(historical, current);

        Assert.Empty(result.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(OnlyAtomId(result)));
    }

    [Theory]
    [InlineData("## Theorem 1\n\n[\nformula\n]\n\nconclusion\n\nappended block\n")]
    [InlineData("## Theorem 1\n\nconclusion\n\nappended block\n")]
    public void Review3996RejectsReorderedOrDeletedHistoricalBody(string current)
    {
        const string historical = "## Theorem 1\n\nconclusion\n\n[\nformula\n]\n";

        var result = EvaluateHistoricalBlockReplay(historical, current);

        Assert.Empty(result.Findings);
        Assert.Equal(
            DigestionReceiptAlignment.Rejected,
            result.AlignmentFor(OnlyAtomId(result)));
    }

    private static DigestionLedgerAlignment EvaluateHistoricalBlockReplay(
        string historicalSource,
        string currentSource)
    {
        var historicalBytes = Encoding.UTF8.GetBytes(historicalSource);
        var currentBytes = Encoding.UTF8.GetBytes(currentSource);
        var historical = Atom("historical", historicalBytes);
        var current = Atom("current", currentBytes);
        var capture = DigestionCasStore.Capture(historical.RawBytes.AsSpan());
        var entry = Entry("historical", historical);
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

        return DigestionLedgerAligner.Evaluate(
            candidate,
            Snapshot(currentBytes, [capture]),
            baseline,
            DigestionAlignmentMode.Admission,
            _ => (_, _) => Atomized(current));
    }

    private static string OnlyAtomId(DigestionLedgerAlignment alignment) =>
        Assert.Single(alignment.EntryAlignments).Key;

    private static RepositorySnapshot DecodeSnapshot(params RawRepositoryEntry[] entries) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(RawRepositorySnapshot.Create(entries))).Snapshot;

    private sealed record ReplayExitFixture(
        string AtomId,
        byte[] CurrentBytes,
        DigestionCasObject Capture,
        BackfillInventoryDocument Baseline,
        BackfillInventoryDocument Candidate)
    {
        internal static ReplayExitFixture Create(
            string atomizer = AtomizerRegistry.GictId)
        {
            var historicalBytes = Encoding.UTF8.GetBytes("historical fine receipt\n");
            var currentBytes = Encoding.UTF8.GetBytes("rewritten source\n");
            var historical = Atom("historical", historicalBytes);
            var atomId = DigestionAlignmentTests.AtomId(historical);
            var capture = DigestionCasStore.Capture(historical.RawBytes.AsSpan());
            var entry = DigestionTestSupport.Entry(
                historical,
                atomId,
                atomizer,
                casRef: capture.Reference);
            var baseline = DigestionTestSupport.Document(
                atomizer,
                [entry with
                {
                    ProjectedStatus = new DigestionStatus(
                        DigestionMigrationState.Partial,
                        DigestionTruthState.Open),
                }]);
            var candidate = DigestionTestSupport.Document(
                atomizer,
                [entry with
                {
                    ProjectedStatus = new DigestionStatus(
                        DigestionMigrationState.Absorbed,
                        DigestionTruthState.Open),
                }]);
            return new ReplayExitFixture(
                atomId,
                currentBytes,
                capture,
                baseline,
                candidate);
        }

        internal DigestionLedgerAlignment Evaluate(
            RepositorySnapshot snapshot,
            Func<string, TheoryAtomizer>? resolver = null) =>
            DigestionLedgerAligner.Evaluate(
                Candidate,
                snapshot,
                Baseline,
                DigestionAlignmentMode.Admission,
                resolver);
    }
}
