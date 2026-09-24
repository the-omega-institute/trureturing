using System.Text.Json;
using StrataLint.Engine;
using Xunit.Abstractions;
using static StrataLint.Tests.ParentSettlementTests;

namespace StrataLint.Tests;

public sealed class Sl016ObservationAdmissionTests(ITestOutputHelper output)
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void UnregisteredTheoryDoesNotSuppressParentStatusAdmission(bool unregisteredTheory, bool reopenChild)
    {
        var fixture = Create();
        var parent = Target(fixture);
        ReplaceFile(fixture, EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest());
        if (unregisteredTheory)
            ReplaceFile(fixture, "docs/develop/theory/UNREGISTERED.md", "# Undigested theory\n");
        var baseline = fixture.Current;
        var neighbors = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var set = SettleAtomCommandTests.Run(temporary.Path, fixture.Current,
            Request(parent.AtomId, neighbors.Previous?.AtomId, neighbors.Next?.AtomId));
        Assert.True(set.Success, set.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        if (reopenChild)
        {
            var clear = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "",
                ["--clear", parent.Receipts.ChainAtoms[0], "--base", "baseline"]);
            Assert.True(clear.Success, clear.Error);
            Assert.Contains("SETTLE_ALIGN_REQUIRED ancestors=" + parent.AtomId, clear.Output, StringComparison.Ordinal);
            fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        }

        var before = baseline.Entries.ToDictionary(e => e.Path, StringComparer.Ordinal);
        var after = fixture.Current.Entries.ToDictionary(e => e.Path, StringComparer.Ordinal);
        var changes = RawChangeSet.CreateWithKinds(before.Keys.Union(after.Keys)
            .Where(path => !before.TryGetValue(path, out var prior) || !after.TryGetValue(path, out var next)
                || !prior.Bytes.AsSpan().SequenceEqual(next.Bytes.AsSpan()))
            .Select(path => (path, !after.ContainsKey(path) ? RawChangeKind.Deleted
                : !before.ContainsKey(path) ? RawChangeKind.Added : RawChangeKind.Modified)));
        Assert.All(changes.Paths, path => Assert.True(BackfillInventoryLoader.IsCanonicalPath(path.Value)));
        var policy = new RuleFixture().Build(RawChangeSet.Create([])).Policy;
        var meta = Assert.IsType<BootstrapOutcome.Clear>(BootstrapGate.Evaluate(changes)).Capability;
        var context = DeltaRuleContext.Create(fixture.Snapshot, DecomposeFixture.Decode(baseline), policy,
            DigestionTestSupport.AcceptedLean(Array.Empty<string>()), changes, meta);

        // Exercise the production delta selector, candidate/baseline loader, impact
        // selection and diagnostic stamping, not only the status evaluator.
        var outcome = RuleCatalog.Default.ExecuteDelta(context);
        Assert.True(outcome is RuleExecutionOutcome.Completed, outcome.ToString());
        var result = Assert.IsType<RuleExecutionOutcome.Completed>(outcome).Capability;
        output.WriteLine(JsonSerializer.Serialize(new { unregisteredTheory, reopenChild,
            changes = changes.Entries, executed = result.ExecutedRules, diagnostics = result.Diagnostics }));
        Assert.Contains(RuleId.CreateKnown(16), result.ExecutedRules);
        var observations = result.Diagnostics.Where(d => d.RuleId == RuleId.CreateKnown(16)
            && d.AdmissionEffect == AdmissionEffect.Observe
            && d.Message.Contains("has no digestion source", StringComparison.Ordinal)).ToArray();
        Assert.Equal(unregisteredTheory ? 1 : 0, observations.Length);
        if (unregisteredTheory)
            Assert.Contains("UNREGISTERED.md' has no digestion source", observations[0].Message, StringComparison.Ordinal);
        var blockers = result.Diagnostics.Where(d => d.AdmissionEffect == AdmissionEffect.Block).ToArray();
        if (reopenChild)
        {
            var mismatch = Assert.Single(blockers);
            Assert.Equal(RuleId.CreateKnown(16), mismatch.RuleId);
            Assert.Equal($"entry {parent.AtomId} handwritten status nonpropositional-inapplicable differs from derived partial-open",
                mismatch.Message);
        }
        else Assert.Empty(blockers);
    }
}
