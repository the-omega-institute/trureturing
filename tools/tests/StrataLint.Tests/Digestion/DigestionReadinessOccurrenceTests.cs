using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class DigestionReadinessOccurrenceTests
{
    [Theory]
    [InlineData("Residual", "Open")]
    [InlineData("Partial", "Closed")]
    public void MissingOccurrenceReportsNonFatalGapForEligibleStatus(
        string migration, string truth)
    {
        var fixture = Create();
        var entry = fixture.Ledger.RequireDigestionEntries()[0];
        fixture = fixture with { SourceBytes = Encoding.UTF8.GetBytes("## Other\n\nChanged.\n") };

        var gap = Assert.Single(Query(fixture, [Evaluate(entry, new(Enum.Parse<DigestionMigrationState>(migration), Enum.Parse<DigestionTruthState>(truth)))]));

        Assert.Equal(entry.AtomId, gap.AtomId);
        Assert.Equal(new DigestionGap("source-occurrence-missing", entry.SourceId,
            DigestionGapSeverity.NonFatal), gap.Gap);
    }

    [Theory]
    [InlineData("Absorbed", "Closed")]
    [InlineData("Nonpropositional", "Inapplicable")]
    [InlineData("Residual", "Closed")]
    [InlineData("Partial", "Open")]
    public void MissingOccurrenceDoesNotReportForExcludedStatus(
        string migration, string truth)
    {
        var fixture = Create();
        var entry = fixture.Ledger.RequireDigestionEntries()[0];
        fixture = fixture with { SourceBytes = [] };

        Assert.Empty(Query(fixture, [Evaluate(entry, new(Enum.Parse<DigestionMigrationState>(migration), Enum.Parse<DigestionTruthState>(truth)))]));
    }

    [Fact]
    public void SameSourceTwoEntriesMaterializeExactlyOnce()
    {
        var fixture = Create();
        var snapshot = fixture.Snapshot();
        var entries = fixture.Ledger.RequireDigestionEntries().Take(2).Select(entry => Evaluate(entry));
        var calls = 0;

        var gaps = DigestionReadinessQuery.SourceOccurrenceGaps(entries, sourceId =>
        {
            calls++;
            return DigestionAtomContextProjection.MaterializeSource(snapshot, fixture.Ledger, sourceId);
        });

        Assert.Empty(gaps);
        Assert.Equal(1, calls);
    }

    [Fact]
    public void PresentOccurrencesIncludeDuplicatesAndDoNotUseLedgerCountDifference()
    {
        var fixture = Create();
        fixture = fixture with { SourceBytes = Encoding.UTF8.GetBytes(ThreeClaims + ThreeClaims) };

        Assert.Empty(Query(fixture, fixture.Ledger.RequireDigestionEntries().Select(entry => Evaluate(entry))));
    }

    [Fact]
    public void ExpandedChainChildrenArePresentAndReplacedParentIsMissing()
    {
        var fixture = Create(ListClaims, expand: true);
        var parent = Assert.Single(fixture.Atomized.ClausePlans).Parent;

        var gap = Assert.Single(Query(fixture,
            fixture.Ledger.RequireDigestionEntries().Select(entry => Evaluate(entry))));

        Assert.Equal(Id(parent), gap.AtomId);
    }

    [Fact]
    public void MembershipIsScopedToTheEntriesOwnSource()
    {
        var fixture = Create();
        var source = fixture.Ledger.RequireDigestionSources().Single();
        var entry = source.Entries[0];
        var other = source with { SourceId = "other", SourcePath = "docs/other.md",
            Entries = [entry with { SourceId = "other", SourcePath = "docs/other.md" }] };
        var ledger = fixture.Ledger.WithDigestionSources([source with { Entries = [] }, other]);
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(fixture.RawSnapshot().Entries.Add(
                RawRepositoryEntry.FromText("docs/other.md", "## Other\n\nChanged.\n"))))).Snapshot;

        var gap = Assert.Single(DigestionReadinessQuery.SourceOccurrenceGaps(
            [Evaluate(other.Entries[0])], sourceId =>
                DigestionAtomContextProjection.MaterializeSource(snapshot, ledger, sourceId)));

        Assert.Equal(entry.AtomId, gap.AtomId);
        Assert.Equal("other", gap.Gap.Detail);
    }

    private static ImmutableArray<(string AtomId, DigestionGap Gap)> Query(
        AtomContextFixture fixture, IEnumerable<DigestionEntryEvaluation> entries)
    {
        var snapshot = fixture.Snapshot();
        return DigestionReadinessQuery.SourceOccurrenceGaps(entries, sourceId =>
            DigestionAtomContextProjection.MaterializeSource(snapshot, fixture.Ledger, sourceId));
    }

    private static DigestionEntryEvaluation Evaluate(DigestionLedgerEntry entry, DigestionStatus? status = null) =>
        new(entry, DigestionReceiptAlignment.Seen, status ?? entry.ProjectedStatus, false, []);
}
