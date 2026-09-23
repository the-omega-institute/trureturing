using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.DigestionTestSupport;
using static StrataLint.Tests.NonpropositionalTestSupport;
using static StrataLint.Tests.ParentSettlementTests;

namespace StrataLint.Tests;

public sealed partial class DigestionLedgerTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void ParentSettlementValidatesCoveredDescendantThroughProductionReportSource(bool batch, bool wrongTarget)
    {
        var fixture = Create();
        var parent = Target(fixture);
        var child = fixture.Document.RequireDigestionEntries().Single(e => e.AtomId == parent.Receipts.ChainAtoms[0]);
        const string gid = "D5/S0/Carrier/Probe";
        const string path = gid + ".lean";
        fixture.Replace(child with
        {
            Coverage = [new(gid, wrongTarget ? "sha256:" + new string('f', 64) : TestModuleStatementId)],
            Receipts = child.Receipts with { Nonpropositional = null },
            ProjectedStatus = new(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries
            .Append(RawRepositoryEntry.FromText(path, Lean(gid)))
            .Concat(FrozenLedgerFiles(path, "probe").Select(file => new RawRepositoryEntry(file.Path, [.. file.Bytes]))));
        using var temporary = new TemporaryDirectory();
        using var requests = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        var request = Request(parent.AtomId, context.Previous?.AtomId, context.Next?.AtomId);
        var requestPath = Path.Combine(requests.Path, "request.toml");
        TemporaryFileSystem.File.WriteAllText(requestPath, (batch ? "[[requests]]\n" : "") + request, new UTF8Encoding(false));
        var report = new FakeLeanReportSource(AcceptedLean(path).Report);
        var environment = new ProductionCliEnvironment(temporary.Path, fixture.Gateway, report);
        var console = new BufferedConsole();
        var before = SettleAtomCommandTests.Image(temporary);
        var result = CliApplication.Run(batch
            ? ["settle-batch", "--requests", requestPath, "--base", "baseline"]
            : ["settle-atom", "--request", requestPath, "--base", "baseline"], environment, console);
        Assert.Equal(1, report.CallCount);
        if (wrongTarget)
        {
            Assert.NotEqual(0, result);
            Assert.Contains("SETTLE_INVALID CHAIN_INCOMPLETE", console.Error, StringComparison.Ordinal);
            Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
        }
        else
        {
            Assert.True(result == 0, console.Error);
            Assert.Contains("SETTLED_NONPROPOSITIONAL atom_id=" + parent.AtomId, console.Output, StringComparison.Ordinal);
        }
    }

    [Fact]
    public void NestedDescendantClearReopensAllReceiptedAncestorsAndCanonicalAlignmentPreservesReceipts()
    {
        var fixture = Create(nested: true);
        var parent = Target(fixture);
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        var policy = new RuleFixture();
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Concat(
            policy.Files.Where(e => e.Key is "Meta/registry.yaml" or "Meta/domains.yaml")
                .Select(e => RawRepositoryEntry.FromText(e.Key, e.Value))));
        ReplaceFile(fixture, EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest());
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        var settled = SettleAtomCommandTests.Run(temporary.Path, fixture.Current,
            Request(parent.AtomId, context.Previous?.AtomId, context.Next?.AtomId));
        Assert.True(settled.Success, settled.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        var baseline = fixture.Current;
        var nested = fixture.Document.RequireDigestionEntries().Single(e => e.AtomId != parent.AtomId && !e.Receipts.ChainAtoms.IsEmpty);
        var childId = nested.Receipts.ChainAtoms[0];
        var clear = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "", ["--clear", childId, "--base", "baseline"]);
        Assert.True(clear.Success, clear.Error);
        var ids = new[] { nested.AtomId, parent.AtomId }.Order(StringComparer.Ordinal).ToArray();
        Assert.Contains("SETTLE_ALIGN_REQUIRED ancestors=" + string.Join(',', ids), clear.Output, StringComparison.Ordinal);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        var evaluation = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan, fixture.Document,
            fixture.Snapshot, AcceptedLean(Array.Empty<string>()), baselineDocument: fixture.Document);
        var uncovered = DigestionStatusEvaluator.EvaluateUncovered(DigestionEvaluationScope.FullScan,
            fixture.Document, fixture.Snapshot, baselineDocument: fixture.Document);
        var clearedChild = fixture.Document.RequireDigestionEntries().Single(e => e.AtomId == childId);
        var changes = RawChangeSet.CreateWithKinds([
            (PathFor(clearedChild, State), RawChangeKind.Deleted),
            (PathFor(clearedChild), RawChangeKind.Added),
        ]);
        var delta = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.ChangedSet, fixture.Document,
            fixture.Snapshot, AcceptedLean(Array.Empty<string>()),
            baselineDocument: BackfillInventoryLoader.Load(Decode(baseline)), baselineSnapshot: Decode(baseline), changes: changes);
        foreach (var id in ids)
        {
            Assert.Equal("partial-open", StateName(delta.Entries.Single(e => e.Entry.AtomId == id).DerivedStatus));
            Assert.Contains(delta.Findings, f => f.StartsWith("entry " + id + " handwritten status", StringComparison.Ordinal));
            Assert.Equal("partial-open", StateName(evaluation.Entries.Single(e => e.Entry.AtomId == id).DerivedStatus));
            Assert.Equal("partial-open", StateName(uncovered.Entries.Single(e => e.Entry.AtomId == id).DerivedStatus));
            Assert.Contains(evaluation.Findings, f => f.StartsWith("entry " + id + " handwritten status", StringComparison.Ordinal));
        }
        var aligned = IngestCommand.Run(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), fixture.Current, baseline),
            new FakeLeanReportSource(AcceptedLean(Array.Empty<string>()).Report),
            new FakeScribeEmissionVerifier(VerifiedScribeEmissions.Empty), ["--base", "baseline"]);
        Assert.True(aligned.Success, aligned.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        foreach (var id in ids)
        {
            var entry = fixture.Document.RequireDigestionEntries().Single(e => e.AtomId == id);
            Assert.Equal("partial-open", StateName(entry.ProjectedStatus));
            Assert.NotNull(entry.Receipts.Nonpropositional);
        }
        var clearedParent = SettleAtomCommandTests.Run(temporary.Path, fixture.Current, "", ["--clear", parent.AtomId, "--base", "baseline"]);
        Assert.True(clearedParent.Success, clearedParent.Error);
        fixture.Current = SettleAtomCommandTests.ReadFiles(temporary);
        Assert.Null(Target(fixture).Receipts.Nonpropositional);
        Assert.Equal(parent.Receipts.ChainAtoms.ToArray(), Target(fixture).Receipts.ChainAtoms.ToArray());
        Assert.NotNull(fixture.Document.RequireDigestionEntries().Single(e => e.AtomId == nested.AtomId).Receipts.Nonpropositional);
    }

    [Theory]
    [InlineData("round-trip", "ROUND_TRIP_FAILED")]
    [InlineData("concurrent", "INFRASTRUCTURE")]
    [InlineData("io", "INFRASTRUCTURE")]
    public void ParentSettlementRetainsAtomicFailureContracts(string failure, string code)
    {
        var fixture = Create();
        var parent = Target(fixture);
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        if (failure == "concurrent")
            TemporaryFileSystem.File.AppendAllText(Path.Combine(temporary.Path, PathFor(parent)), "\n", Encoding.UTF8);
        var before = SettleAtomCommandTests.Image(temporary);
        var calls = 0;
        var serializations = 0;
        var result = SettleAtomCommandTests.Run(temporary.Path, fixture.Current,
            Request(parent.AtomId, context.Previous?.AtomId, context.Next?.AtomId),
            apply: (root, current, updates) =>
            {
                calls++;
                Assert.Equal(2, updates.Length);
                IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates, (pending, destination) =>
                {
                    File.Move(pending, destination, true);
                    if (failure == "io") throw new IOException("simulated parent update failure");
                });
            }, writer: entry => failure == "round-trip"
                ? [.. BackfillInventoryWriter.WriteAtom(entry), .. Encoding.UTF8.GetBytes(new string('\n', ++serializations))]
                : BackfillInventoryWriter.WriteAtom(entry));
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID " + code, result.Error, StringComparison.Ordinal);
        Assert.Equal(failure == "round-trip" ? 0 : 1, calls);
        Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
    }
}
