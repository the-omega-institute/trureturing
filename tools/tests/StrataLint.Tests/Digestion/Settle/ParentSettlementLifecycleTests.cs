using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
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
    public void MixedParentFrontierSurvivesSetAndClearThroughProductionRoute(bool nested, bool fullScan)
    {
        var fixture = Create(nested);
        var parent = Target(fixture);
        AddCoveredLeaf(fixture);
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        var residualText = Encoding.UTF8.GetString(context.Previous!.Value.RawBytes.AsSpan());
        var residual = DecomposeFixture.Entry(residualText);
        fixture.Add(residual, residualText);
        ReplaceFile(fixture, EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest());
        using var temporary = new TemporaryDirectory();
        using var requests = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        WriteParentReport(temporary, fixture);
        var baseline = ReadParentFiles(temporary);
        var requestPath = WriteParentRequest(requests, parent, context, batch: false);
        var before = RunParentCli(temporary, baseline, fullScan, "digest-status", "--formalize-candidates", "--base", "baseline");
        var set = RunParentCli(temporary, baseline, fullScan, "settle-atom", "--request", requestPath, "--base", "baseline");
        Assert.True(set.Exit == 0, set.Error);
        fixture.Current = ReadParentFiles(temporary);
        AssertParentOnlyChanged(baseline, fixture.Current, parent.AtomId);
        var full = DigestionStatusEvaluator.Evaluate(DigestionEvaluationScope.FullScan, fixture.Document,
            fixture.Snapshot, Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(
                fixture.Snapshot, new PrecomputedLeanReportSource(temporary.Path).Load(fixture.Snapshot))).Capability);
        Assert.Empty(full.Findings);
        Assert.Equal(State, StateName(full.Entries.Single(e => e.Entry.AtomId == parent.AtomId).DerivedStatus));
        var after = RunParentCli(temporary, baseline, fullScan, "digest-status", "--formalize-candidates", "--base", "baseline");
        var clear = RunParentCli(temporary, baseline, fullScan, "settle-atom", "--clear", parent.AtomId, "--base", "baseline");
        Assert.True(clear.Exit == 0, clear.Error);
        AssertParentOnlyChanged(baseline, ReadParentFiles(temporary), parent.AtomId);
        var cleared = RunParentCli(temporary, baseline, fullScan, "digest-status", "--formalize-candidates", "--base", "baseline");
        Assert.True(new[] { before.Exit, after.Exit, cleared.Exit }.SequenceEqual([0, 0, 0]),
            $"frontier exits={before.Exit}/{after.Exit}/{cleared.Exit}\n{before.Error}{after.Error}{cleared.Error}");
        AssertCandidates(before.Output, parent.AtomId, residual.AtomId);
        AssertCandidates(after.Output, residual.AtomId);
        AssertCandidates(cleared.Output, parent.AtomId, residual.AtomId);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void UncoveredParentSettlementIgnoresUnrelatedManagedLeanThroughProductionRoute(bool batch, bool unrelatedLean)
    {
        var fixture = Create(nested: true);
        var parent = Target(fixture);
        if (unrelatedLean) ReplaceFile(fixture, "D5/S0/Carrier/Unrelated.lean", Lean("D5/S0/Carrier/Unrelated"));
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        using var temporary = new TemporaryDirectory();
        using var requests = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        WriteParentReport(temporary, fixture);
        var baseline = ReadParentFiles(temporary);
        var requestPath = WriteParentRequest(requests, parent, context, batch);
        var result = RunParentCli(temporary, baseline, false,
            batch ? "settle-batch" : "settle-atom", batch ? "--requests" : "--request", requestPath, "--base", "baseline");
        Assert.True(result.Exit == 0, result.Error);
        fixture.Current = ReadParentFiles(temporary);
        Assert.Equal(State, StateName(Target(fixture).ProjectedStatus));
        AssertParentOnlyChanged(baseline, fixture.Current, parent.AtomId);
    }

    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void MixedParentFrontierRejectsReopenedDescendantWithoutWriting(bool fullScan, bool coveredBranch)
    {
        var fixture = Create(nested: true);
        var parent = Target(fixture);
        if (coveredBranch)
            AddParentCoverage(fixture, fixture.Document.RequireDigestionEntries().Single(e =>
                e.AtomId != parent.AtomId && !e.Receipts.ChainAtoms.IsEmpty));
        else AddCoveredLeaf(fixture);
        ReplaceFile(fixture, EngineeringRegistrationFixture.Path, EngineeringRegistrationFixture.Manifest());
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        using var temporary = new TemporaryDirectory();
        using var requests = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        WriteParentReport(temporary, fixture);
        var baseline = ReadParentFiles(temporary);
        var requestPath = WriteParentRequest(requests, parent, context, batch: false);
        var set = RunParentCli(temporary, baseline, fullScan, "settle-atom", "--request", requestPath, "--base", "baseline");
        Assert.True(set.Exit == 0, set.Error);
        var settledQuery = RunParentCli(temporary, baseline, fullScan, "digest-status", "--formalize-candidates", "--base", "baseline");
        Assert.True(settledQuery.Exit == 0, settledQuery.Error);
        fixture.Current = ReadParentFiles(temporary);
        var branch = fixture.Document.RequireDigestionEntries().Single(e => e.AtomId != parent.AtomId
            && !e.Receipts.ChainAtoms.IsEmpty);
        var child = fixture.Document.RequireDigestionEntries().First(e => branch.Receipts.ChainAtoms.Contains(e.AtomId)
            && e.Receipts.Nonpropositional is not null);
        var clear = RunParentCli(temporary, baseline, fullScan, "settle-atom", "--clear", child.AtomId, "--base", "baseline");
        Assert.True(clear.Exit == 0, clear.Error);
        Assert.Contains(parent.AtomId, clear.Output, StringComparison.Ordinal);
        var before = SettleAtomCommandTests.Image(temporary);
        var query = RunParentCli(temporary, baseline, fullScan, "digest-status", "--formalize-candidates", "--base", "baseline");
        Assert.Equal(2, query.Exit);
        Assert.Contains("entry " + parent.AtomId + " handwritten status", query.Error, StringComparison.Ordinal);
        Assert.Contains("differs from derived partial-open", query.Error, StringComparison.Ordinal);
        Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
        Assert.Equal(0, RunParentCli(temporary, baseline, fullScan, "settle-atom", "--clear", parent.AtomId, "--base", "baseline").Exit);
        before = SettleAtomCommandTests.Image(temporary);
        var reset = RunParentCli(temporary, baseline, fullScan, "settle-atom", "--request", requestPath, "--base", "baseline");
        Assert.Equal(2, reset.Exit);
        Assert.Contains("SETTLE_INVALID CHAIN_INCOMPLETE", reset.Error, StringComparison.Ordinal);
        Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
    }

    [Theory]
    [InlineData(false, "valid")]
    [InlineData(true, "valid")]
    [InlineData(false, "wrong-target")]
    [InlineData(true, "wrong-target")]
    [InlineData(false, "stale-report")]
    [InlineData(true, "stale-report")]
    [InlineData(false, "missing-report")]
    [InlineData(true, "missing-report")]
    [InlineData(false, "open-report")]
    [InlineData(true, "open-report")]
    public void ParentSettlementValidatesCoveredDescendantThroughProductionReportSource(bool batch, string evidence)
    {
        var fixture = Create();
        var parent = Target(fixture);
        var child = fixture.Document.RequireDigestionEntries().Single(e => e.AtomId == parent.Receipts.ChainAtoms[0]);
        const string gid = "D5/S0/Carrier/Probe";
        const string path = gid + ".lean";
        fixture.Replace(child with
        {
            Coverage = [new(gid, evidence == "wrong-target" ? "sha256:" + new string('f', 64) : TestModuleStatementId)],
            Receipts = child.Receipts with { Nonpropositional = null },
            ProjectedStatus = new(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries
            .Append(RawRepositoryEntry.FromText(path, Lean(gid)))
            .Concat(FrozenLedgerFiles(path, "probe").Select(file => new RawRepositoryEntry(file.Path, [.. file.Bytes]))));
        using var temporary = new TemporaryDirectory();
        using var requests = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        WriteParentReport(temporary, fixture);
        var reportPath = RawLeanReportArtifact.DefaultPath(temporary.Path);
        if (evidence == "missing-report") File.Delete(reportPath);
        if (evidence == "stale-report")
        {
            ReplaceFile(fixture, path, Lean(gid) + "\n-- source changed after report\n");
            SettleAtomCommandTests.WriteFiles(temporary.Path, fixture.Current);
        }
        if (evidence == "open-report")
            RawLeanReportArtifact.WriteFile(reportPath, fixture.Snapshot, AcceptedLean((path,
                new LeanFileReport([], [new LeanDeclaration("probe", "theorem", "True", ["sorryAx"])]))).Report);
        var context = DigestionAtomContextProjection.Resolve(fixture.Snapshot, fixture.Document, parent.AtomId);
        var request = Request(parent.AtomId, context.Previous?.AtomId, context.Next?.AtomId);
        var requestPath = Path.Combine(requests.Path, "request.toml");
        TemporaryFileSystem.File.WriteAllText(requestPath, (batch ? "[[requests]]\n" : "") + request, new UTF8Encoding(false));
        var before = SettleAtomCommandTests.Image(temporary);
        var result = RunParentCli(temporary, fixture.Current, false,
            batch ? "settle-batch" : "settle-atom", batch ? "--requests" : "--request", requestPath, "--base", "baseline");
        if (evidence != "valid")
        {
            Assert.Equal(2, result.Exit);
            Assert.Contains(evidence is "wrong-target" or "open-report" ? "SETTLE_INVALID CHAIN_INCOMPLETE"
                : "SETTLE_INVALID INFRASTRUCTURE", result.Error, StringComparison.Ordinal);
            Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
        }
        else
        {
            Assert.True(result.Exit == 0, result.Error);
            Assert.Contains("SETTLED_NONPROPOSITIONAL atom_id=" + parent.AtomId, result.Output, StringComparison.Ordinal);
            AssertParentOnlyChanged(fixture.Current, ReadParentFiles(temporary), parent.AtomId);
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

    private static RawRepositorySnapshot ReadParentFiles(TemporaryDirectory temporary) =>
        RawRepositorySnapshot.Create(SettleAtomCommandTests.ReadFiles(temporary).Entries
            .Where(e => !e.Path.StartsWith(".lake/", StringComparison.Ordinal)));

    private static void AddCoveredLeaf(DecomposeFixture fixture)
    {
        var entries = fixture.Document.RequireDigestionEntries();
        var nested = entries.FirstOrDefault(e => e.AtomId != fixture.Parent.AtomId && !e.Receipts.ChainAtoms.IsEmpty);
        var child = entries.First(e => e.Receipts.ChainAtoms.IsEmpty
            && (nested is null || nested.Receipts.ChainAtoms.Contains(e.AtomId)));
        AddParentCoverage(fixture, child);
    }

    private static void AddParentCoverage(DecomposeFixture fixture, DigestionLedgerEntry child)
    {
        const string gid = "D5/S0/Carrier/Probe";
        const string path = gid + ".lean";
        fixture.Replace(child with
        {
            Coverage = [new(gid, TestModuleStatementId)],
            Receipts = child.Receipts with { Nonpropositional = null },
            ProjectedStatus = new(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
        });
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries
            .Append(RawRepositoryEntry.FromText(path, Lean(gid)))
            .Concat(FrozenLedgerFiles(path, "probe").Select(file => new RawRepositoryEntry(file.Path, [.. file.Bytes]))));
    }

    private static void WriteParentReport(TemporaryDirectory temporary, DecomposeFixture fixture)
    {
        var report = AcceptedLean(fixture.Current.Entries.Where(e => LeanClosureValidator.IsManagedLean(e.Path))
            .Select(e => e.Path).ToArray()).Report;
        RawLeanReportArtifact.WriteFile(RawLeanReportArtifact.DefaultPath(temporary.Path), fixture.Snapshot, report);
        Assert.IsType<LeanValidationOutcome.Accepted>(LeanClosureValidator.Validate(fixture.Snapshot,
            new PrecomputedLeanReportSource(temporary.Path).Load(fixture.Snapshot)));
    }

    private static string WriteParentRequest(TemporaryDirectory requests, DigestionLedgerEntry parent,
        DigestionAtomContext context, bool batch)
    {
        var path = Path.Combine(requests.Path, "request.toml");
        TemporaryFileSystem.File.WriteAllText(path, (batch ? "[[requests]]\n" : "")
            + Request(parent.AtomId, context.Previous?.AtomId, context.Next?.AtomId), new UTF8Encoding(false));
        return path;
    }

    private static (int Exit, string Output, string Error) RunParentCli(TemporaryDirectory temporary,
        RawRepositorySnapshot baseline, bool fullScan, params string[] arguments)
    {
        var current = ReadParentFiles(temporary);
        var changes = RawChangeSet.Create(fullScan ? [] : current.Entries.Concat(baseline.Entries)
            .Select(e => e.Path).Distinct(StringComparer.Ordinal).Where(path =>
            {
                var before = baseline.Entries.FirstOrDefault(e => e.Path == path);
                var after = current.Entries.FirstOrDefault(e => e.Path == path);
                return before is null || after is null || !before.Bytes.AsSpan().SequenceEqual(after.Bytes.AsSpan());
            }).DefaultIfEmpty(DecomposeFixture.PathFor(BackfillInventoryLoader.Load(Decode(current))
                .RequireDigestionEntries().First())));
        var repository = new FakeRepositoryGateway(changes, current, baseline,
            currentReader: () => ReadParentFiles(temporary));
        var environment = new ProductionCliEnvironment(temporary.Path, repository, new PrecomputedLeanReportSource(temporary.Path));
        var console = new BufferedConsole();
        var image = SettleAtomCommandTests.Image(temporary);
        var reading = RawLeanReportArtifact.Reading.Value;
        try
        {
            if (arguments[0] == "digest-status")
                RawLeanReportArtifact.Reading.Value = () => throw new InvalidOperationException("global frontier must not load Lean evidence");
            var exit = CliApplication.Run(arguments, environment, console);
            if (arguments[0] == "digest-status") Assert.Equal(image, SettleAtomCommandTests.Image(temporary));
            return (exit, console.Output, console.Error);
        }
        finally { RawLeanReportArtifact.Reading.Value = reading; }
    }

    private static void AssertCandidates(string output, params string[] expected)
    {
        using var json = JsonDocument.Parse(output);
        Assert.Equal(expected.Order(StringComparer.Ordinal), json.RootElement.GetProperty("candidates")
            .EnumerateArray().Select(e => e.GetProperty("atom_id").GetString()).Order(StringComparer.Ordinal));
    }

    private static void AssertParentOnlyChanged(RawRepositorySnapshot before, RawRepositorySnapshot after, string id) =>
        Assert.Equal(before.Entries.Where(e => !e.Path.EndsWith("/" + id + ".yaml", StringComparison.Ordinal))
                .Select(e => (e.Path, Convert.ToHexString(e.Bytes.AsSpan()))).OrderBy(e => e.Path),
            after.Entries.Where(e => !e.Path.EndsWith("/" + id + ".yaml", StringComparison.Ordinal))
                .Select(e => (e.Path, Convert.ToHexString(e.Bytes.AsSpan()))).OrderBy(e => e.Path));
}
