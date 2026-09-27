using System.Text;
using StrataLint.Engine;

namespace StrataLint.Rules.Tests;

public sealed class Sl016ObservationStatusTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void UnrelatedObservationDoesNotSuppressStatusMismatch(
        bool hasUnregisteredTheory,
        bool hasStaleStatus)
    {
        const string unregisteredPath = "docs/develop/theory/UNREGISTERED.md";
        var fixture = new RuleFixture();
        var initial = fixture.Build(RawChangeSet.Create([]));
        var entry = Assert.Single(BackfillInventoryLoader.Load(initial.Current)
            .RequireDigestionEntries()) with { Coverage = [] };
        var residualPath = $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/residual-open/{entry.AtomId}.yaml";
        var closedPath = $"{BackfillInventoryLoader.RootPath}{entry.SourceId}/absorbed-closed/{entry.AtomId}.yaml";
        fixture.Files.Remove(RuleFixture.FixtureBackfillAtomPath);
        fixture.Files[residualPath] = Encoding.UTF8.GetString(
            BackfillInventoryWriter.WriteAtom(entry).AsSpan());
        if (hasUnregisteredTheory)
        {
            fixture.Files[unregisteredPath] = "# Undigested theory\n";
        }

        // Both snapshots start with a valid uncovered leaf and the same unrelated observation.
        fixture.Baseline.Clear();
        foreach (var (path, text) in fixture.Files)
        {
            fixture.Baseline.Add(path, text);
        }

        // Change the status authority in every case, including the valid-state controls.
        fixture.Files[RuleFixture.FixtureDigestionSourcePath] += "changed";
        if (hasStaleStatus)
        {
            fixture.Files[closedPath] = fixture.Files[residualPath];
            fixture.Files.Remove(residualPath);
        }

        var changes = RawChangeSet.CreateWithKinds(fixture.Files.Keys
            .Union(fixture.Baseline.Keys, StringComparer.Ordinal)
            .Where(path => !fixture.Files.TryGetValue(path, out var current)
                || !fixture.Baseline.TryGetValue(path, out var baseline)
                || !string.Equals(current, baseline, StringComparison.Ordinal))
            .Select(path => (path, !fixture.Files.ContainsKey(path)
                ? RawChangeKind.Deleted
                : !fixture.Baseline.ContainsKey(path)
                    ? RawChangeKind.Added
                    : RawChangeKind.Modified)));
        var context = fixture.Build(changes);
        Assert.True(BackfillInventoryRule.IsAffectedBy(context));
        var completed = Assert.IsType<RuleExecutionOutcome.Completed>(
            RuleCatalog.Default.ExecuteDelta(context)).Capability;
        var sl016 = RuleId.CreateKnown(16);
        Assert.Contains(sl016, completed.ExecutedRules);
        Assert.DoesNotContain(sl016, completed.SkippedRules);

        var diagnostics = completed.Diagnostics.Where(diagnostic => diagnostic.RuleId == sl016).ToArray();
        var observations = diagnostics.Where(static diagnostic =>
            diagnostic.AdmissionEffect == AdmissionEffect.Observe).ToArray();
        var blocks = diagnostics.Where(static diagnostic =>
            diagnostic.AdmissionEffect == AdmissionEffect.Block).ToArray();
        Assert.Equal(hasUnregisteredTheory ? 1 : 0, observations.Length);
        if (hasUnregisteredTheory)
        {
            Assert.Equal(
                $"theory document '{unregisteredPath}' has no digestion source: run make ingest, "
                    + "which registers it with the default atomizer",
                Assert.Single(observations).Message);
        }
        Assert.Equal(hasStaleStatus ? 1 : 0, blocks.Length);
        if (hasStaleStatus)
        {
            Assert.Equal(
                $"entry {entry.AtomId} handwritten status absorbed-closed differs from derived residual-open",
                Assert.Single(blocks).Message);
        }
        Assert.Equal(observations.Length + blocks.Length, diagnostics.Length);
    }
}
