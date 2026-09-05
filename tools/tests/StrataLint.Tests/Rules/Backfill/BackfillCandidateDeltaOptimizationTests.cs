using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class BackfillCandidateDeltaOptimizationTests
{
    [Fact]
    public void OneContextLoadsCandidateDeltaOnceAcrossWakeupAndEvaluation()
    {
        const string targetPath = "D5/S0/Carrier/BackfillTarget.lean";
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        foreach (var files in new[] { fixture.Files, fixture.Baseline, fixture.ForkPoint })
        {
            FrozenStatementReceiptTestData.AddLedger(
                files,
                new FrozenStatementReceiptTestData.Module(
                    targetPath,
                    FrozenStatementReceiptTestData.Id('a'),
                    []));
        }
        var context = fixture.Build(RawChangeSet.Create([targetPath]));
        var initialDocument = BackfillInventoryLoader.LoadCandidateDelta(
            context.Current,
            context.Baseline,
            context.Changes);
        var impact = BackfillDeltaImpactResolver.Resolve(
            context.Current,
            context.Baseline,
            context.Lean.Report,
            initialDocument,
            context.Changes);

        Assert.DoesNotContain(
            context.Changes.Paths,
            static path => BackfillInventoryLoader.IsCanonicalPath(path.Value));
        var promotedPath = Assert.Single(
            impact.EvaluationChanges.Paths,
            static path => BackfillInventoryLoader.IsCanonicalPath(path.Value));
        Assert.True(context.Current.TryGetFile(promotedPath.Value, out var current));
        Assert.True(context.Baseline.TryGetFile(promotedPath.Value, out var baseline));
        Assert.True(current.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan()));

        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        _ = BackfillInventoryRule.EvaluateCandidateDelta(context);

        Assert.Equal(1, context.BackfillCandidateDeltaLoadCount);
    }

    [Fact]
    public void RuleImplementationChangeInitializesSessionDuringEvaluation()
    {
        var fixture = new RuleFixture();
        fixture.AddBackfillTargets();
        var context = fixture.Build(RawChangeSet.Create(
        [
            "tools/StrataLint.Engine/Rules/Backfill/BackfillInventoryRule.cs",
        ]));

        Assert.True(context.RuleImplementationChanged);
        _ = BackfillInventoryRule.EvaluateCandidateDelta(context);

        Assert.Equal(1, context.BackfillCandidateDeltaLoadCount);
    }

    [Fact]
    public void EquivalentRawChangesShareTheContextDocument()
    {
        var fixture = new RuleFixture();
        var context = fixture.Build(RawChangeSet.CreateWithKinds(
        [
            (RuleFixture.FixtureBackfillAtomPath, RawChangeKind.Modified),
            (RuleFixture.RingPath, RawChangeKind.Copied),
        ]));
        _ = context.BackfillCandidateDeltaSession.GetDocument(context.Changes);
        _ = context.BackfillCandidateDeltaSession.GetDocument(
            RawChangeSet.CreateWithKinds(
            [
                (RuleFixture.RingPath, RawChangeKind.Copied),
                (RuleFixture.FixtureBackfillAtomPath, RawChangeKind.Modified),
            ]));

        Assert.Equal(1, context.BackfillCandidateDeltaLoadCount);
    }

    [Fact]
    public void CandidateDeltaProjectionContainsExactlyTheLoaderInputPartition()
    {
        var snapshot = Snapshot(
            (RuleFixture.FixtureBackfillSourcePath, RuleFixture.FixtureBackfillSource),
            (RuleFixture.FixtureBackfillAtomPath, RuleFixture.FixtureBackfillAtom),
            (BackfillInventoryLoader.RootPath + "not-canonical.txt", "evidence\n"),
            (BackfillInventoryLoader.RelativePath, "legacy\n"),
            (RuleFixture.RingPath, "lean\n"),
            ("D5/S0/Carrier/notes.txt", "outside\n"),
            ("Meta/registry.yaml", "outside\n"),
            ("README.md", "outside\n"));
        var projected = BackfillInventoryLoader.ProjectInputSnapshot(snapshot);

        Assert.Equal(
        [
            RuleFixture.RingPath,
            BackfillInventoryLoader.RelativePath,
            RuleFixture.FixtureBackfillAtomPath,
            RuleFixture.FixtureBackfillSourcePath,
            BackfillInventoryLoader.RootPath + "not-canonical.txt",
        ],
            projected.Files.Keys
                .Select(static path => path.Value)
                .Order(StringComparer.Ordinal)
                .ToArray());
    }

    [Fact]
    public void NoncanonicalPathWithinBackfillRootStillFailsClosedAfterProjection()
    {
        var snapshot = Snapshot(
            (RuleFixture.FixtureBackfillSourcePath, RuleFixture.FixtureBackfillSource),
            (RuleFixture.FixtureBackfillAtomPath, RuleFixture.FixtureBackfillAtom),
            (BackfillInventoryLoader.RootPath + "not-canonical.txt", "evidence\n"));

        var exception = Assert.Throws<FormatException>(() =>
            BackfillInventoryLoader.LoadCandidateDelta(
                snapshot,
                snapshot,
                RawChangeSet.Create([])));

        Assert.Contains("noncanonical digestion ledger path", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void PartitionOutsideFileAbsenceDoesNotChangeCandidateDocument()
    {
        var inputs = new[]
        {
            (RuleFixture.FixtureBackfillSourcePath, RuleFixture.FixtureBackfillSource),
            (RuleFixture.FixtureBackfillAtomPath, RuleFixture.FixtureBackfillAtom),
            ("D5/X_Frontier/Ticket.lean", "/-- TASK D5-T0098 -/\ndef task : Unit := ()\n"),
        };
        var withoutOutside = Snapshot(inputs);
        var withOutside = Snapshot([.. inputs, ("README.md", "outside partition\n")]);

        var first = BackfillInventoryLoader.LoadCandidateDelta(
            withoutOutside,
            withoutOutside,
            RawChangeSet.Create([]));
        var second = BackfillInventoryLoader.LoadCandidateDelta(
            withOutside,
            withOutside,
            RawChangeSet.Create([]));

        Assert.Equal(
            first.RequireDigestionEntries().Select(EntryIdentity),
            second.RequireDigestionEntries().Select(EntryIdentity));
        Assert.Equal(
            first.RequireTickets().Select(TicketIdentity),
            second.RequireTickets().Select(TicketIdentity));
    }

    private static string EntryIdentity(DigestionLedgerEntry entry) =>
        $"{entry.SourceId}/{entry.ProjectedStatus}/{entry.AtomId}/{entry.CasRef}";

    private static string TicketIdentity(BackfillTicketReference ticket) =>
        $"{ticket.CaseId}/{ticket.Gid}";

    private static RepositorySnapshot Snapshot(params (string Path, string Text)[] files) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
            RawRepositorySnapshot.Create(files.Select(static file =>
                RawRepositoryEntry.FromText(file.Path, file.Text))))).Snapshot;
}
