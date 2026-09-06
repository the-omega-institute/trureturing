using StrataLint.Engine;
using static StrataLint.Tests.NonpropositionalTestSupport;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Fact]
    public void NonpropositionalDirectoryWithoutReceiptIsSl016Red()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var entry = fixture.Ledger.RequireDigestionEntries().Single();
        var raw = RawRepositorySnapshot.Create(WithCas(fixture).Entries.Select(item =>
            item.Path == PathFor(entry) ? new RawRepositoryEntry(PathFor(entry, State), item.Bytes) : item));
        var snapshot = Decode(raw);
        var document = BackfillInventoryLoader.Load(snapshot);
        var changes = RawChangeSet.Create([PathFor(entry, State)]);
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.ChangedSet,
            document, snapshot, DigestionTestSupport.AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Ledger,
            changes: changes, casChanges: RawChangeSet.Create([]));
        Assert.Contains(evaluation.Findings, message => message ==
            $"entry {entry.AtomId} handwritten status {State} differs from derived residual-open");
    }

    [Fact]
    public void NonpropositionalReceiptInOtherDirectoryIsSl016Red()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        var original = fixture.Ledger.RequireDigestionEntries().Single();
        var entry = Settled(original) with { ProjectedStatus = original.ProjectedStatus };
        fixture = fixture.WithEntries([entry]);
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Ledger, Decode(WithCas(fixture)), DigestionTestSupport.AcceptedLean(Array.Empty<string>()));
        Assert.Contains(evaluation.Findings, message => message ==
            $"entry {entry.AtomId} handwritten status residual-open differs from derived {State}");
    }

    [Fact]
    public void NonpropositionalDerivesWithoutCoverageAndIsNotDeletable()
    {
        var fixture = AtomContextFixture.Create("## Claim\n\nProse.\n");
        fixture = fixture.WithEntries([Settled(fixture.Ledger.RequireDigestionEntries().Single())]);
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan,
            fixture.Ledger, Decode(WithCas(fixture)), DigestionTestSupport.AcceptedLean(Array.Empty<string>()));
        var item = Assert.Single(evaluation.Entries);
        Assert.Equal(State, StateName(item.DerivedStatus));
        Assert.False(item.Deletable);
        Assert.DoesNotContain(item.Gaps, gap => gap.Code == "coverage-gid-missing");
        Assert.Empty(evaluation.Findings);
    }

    [Fact]
    public void MigrationAndTruthAlphabetsAreTotal()
    {
        Assert.Equal(new[] { "residual", "partial", "absorbed", "nonpropositional" },
            Enum.GetValues<DigestionMigrationState>().Select(DigestionStatusNames.Migration));
        Assert.Equal(new[] { "closed", "tail", "open", "inapplicable" },
            Enum.GetValues<DigestionTruthState>().Select(DigestionStatusNames.Truth));
    }
}
