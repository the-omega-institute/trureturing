using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class ScribeSeedCommandTests
{
    [Theory]
    [InlineData(false, false)]
    [InlineData(true, false)]
    [InlineData(false, true)]
    [InlineData(true, true)]
    public void SeedAcceptsStaleAncestorByteReceipt(bool batch, bool dryRun)
    {
        var fixture = ChainFixture(1, batch);
        var ancestor = Assert.Single(fixture.Document.RequireDigestionEntries(), entry =>
            !entry.Receipts.ChainAtoms.IsEmpty);
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry => entry.AtomId == ancestor.AtomId
            ? entry with
            {
                Receipts = entry.Receipts with
                {
                    Scribe = [entry.Receipts.Scribe[0] with { DefinitionSha256 = "sha256:" + new string('a', 64) }],
                },
            }
            : entry);
        fixture.Baseline = fixture.Document;
        RequireValidChainBaseline(fixture, 1);

        var execution = ExecuteChainSeed(fixture, batch, dryRun);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.DoesNotContain("scribe-definition-mismatch", execution.Result.Error, StringComparison.Ordinal);
        if (dryRun)
        {
            Assert.Equal(0, execution.ApplyCalls);
            Assert.Equal(Image(execution.Before), Image(execution.After));
        }
        else
        {
            RequireProjectedChain(fixture, execution, 1);
        }
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void SeedAcceptsCurrentAncestorReceiptAndAdmissionAcceptsDocuments(bool batch)
    {
        var fixture = ChainFixture(1, batch);
        RequireValidChainBaseline(fixture, 1);

        var execution = ExecuteChainSeed(fixture, batch, dryRun: false);

        RequireProjectedChain(fixture, execution, 1);
        var before = execution.Before.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var after = execution.After.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var changes = RawChangeSet.Create(before.Keys.Union(after.Keys, StringComparer.Ordinal).Where(path =>
            !before.TryGetValue(path, out var oldEntry) || !after.TryGetValue(path, out var newEntry)
            || !oldEntry.Bytes.AsSpan().SequenceEqual(newEntry.Bytes.AsSpan())));
        var current = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(execution.After)).Snapshot;
        var baseline = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(execution.Before)).Snapshot;
        var policy = RegistryLoadAssert.Accepted(RegistryLoader.Load(
            Encoding.UTF8.GetBytes(TestRegistry.Canonical), Encoding.UTF8.GetBytes(TestRegistry.Domains))).Policy;
        var lean = Assert.IsType<LeanValidationOutcome.Accepted>(
            LeanClosureValidator.Validate(current, fixture.Inputs.Report)).Capability;
        var bootstrap = Assert.IsType<BootstrapOutcome.Clear>(BootstrapGate.Evaluate(changes));
        var context = RuleEvaluationContext.Create(current, baseline, policy, lean, changes,
            MetaEvaluationProfile.ForClear(bootstrap.Capability), fixture.Verified);

        var findings = BackfillInventoryRule.EvaluateCandidateDelta(context);

        Assert.Empty(findings);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void SeedChildProjectsDependentParentInSameTransaction(int ancestorCount)
    {
        var fixture = ChainFixture(ancestorCount);
        RequireValidChainBaseline(fixture, ancestorCount);

        var execution = Execute(fixture);

        RequireProjectedChain(fixture, execution, ancestorCount);
    }

    [Theory]
    [InlineData(1)]
    [InlineData(2)]
    public void SeedBatchProjectsDependentChainInSameTransaction(int ancestorCount)
    {
        var fixture = ChainFixture(ancestorCount, batch: true);
        RequireValidChainBaseline(fixture, ancestorCount);
        var children = fixture.Document.RequireDigestionEntries()
            .Where(entry => entry.Receipts.Scribe.IsEmpty && entry.ProjectedStatus.Truth == DigestionTruthState.Closed);
        var pairs = string.Concat(children.Select(entry => $"{entry.AtomId}\t{ScribeSeedFixture.DeclarationGid}\n"));

        var execution = Execute(fixture, BatchArgs(), pairs);

        RequireProjectedChain(fixture, execution, ancestorCount);
    }

    [Theory]
    [InlineData(1, false)]
    [InlineData(2, false)]
    [InlineData(1, true)]
    [InlineData(2, true)]
    public void SeedDryRunReportsDependentChainStatusChangesWithoutWriting(int ancestorCount, bool batch)
    {
        var fixture = ChainFixture(ancestorCount, batch);
        RequireValidChainBaseline(fixture, ancestorCount);
        var affected = fixture.Document.RequireDigestionEntries().Where(entry =>
            entry.ProjectedStatus.Truth == DigestionTruthState.Closed).ToArray();
        var pairs = string.Concat(affected.Where(entry => entry.Receipts.Scribe.IsEmpty)
            .Select(entry => $"{entry.AtomId}\t{ScribeSeedFixture.DeclarationGid}\n"));
        string[] arguments = batch ? [.. BatchArgs(), "--dry-run"]
            : ["--seed-missing", "--atom", fixture.First.AtomId, "--gid",
                ScribeSeedFixture.DeclarationGid, "--base", "baseline", "--dry-run"];

        var execution = Execute(fixture, arguments, pairs);

        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(0, execution.ApplyCalls);
        Assert.Equal(Image(execution.Before), Image(execution.After));
        var statusLines = execution.Result.Output.Split('\n')
            .Where(line => line.StartsWith("SCRIBE_SEED_STATUS ", StringComparison.Ordinal)).ToArray();
        Assert.Equal(affected.Length, statusLines.Length);
        foreach (var entry in affected)
        {
            Assert.Contains($"SCRIBE_SEED_STATUS atom_id={entry.AtomId} from=partial-closed "
                + "to=absorbed-closed dry_run=true ledger_changed=false", statusLines);
        }
    }

    private static SeedExecution ExecuteChainSeed(ScribeSeedFixture fixture, bool batch, bool dryRun)
    {
        var children = fixture.Document.RequireDigestionEntries().Where(entry =>
            entry.Receipts.Scribe.IsEmpty && entry.ProjectedStatus.Truth == DigestionTruthState.Closed);
        var pairs = string.Concat(children.Select(entry => $"{entry.AtomId}\t{ScribeSeedFixture.DeclarationGid}\n"));
        string[] arguments = batch ? BatchArgs()
            : ["--seed-missing", "--atom", fixture.First.AtomId, "--gid",
                ScribeSeedFixture.DeclarationGid, "--base", "baseline"];
        return Execute(fixture, dryRun ? [.. arguments, "--dry-run"] : arguments, pairs);
    }

    private static ScribeSeedFixture ChainFixture(int ancestorCount, bool batch = false)
    {
        var fixture = new ScribeSeedFixture(ancestorCount + (batch ? 3 : 2));
        var entries = fixture.Document.RequireDigestionEntries();
        Assert.True(fixture.Verified.TryGet(ScribeSeedFixture.ModuleGid, out var verified));
        var receipt = new DigestionScribeReceipt(ScribeSeedFixture.DeclarationGid,
            verified.DefinitionSha256, verified.EmissionSha256);
        fixture.Document = ScribeSeedFixture.Map(fixture.Document, entry =>
        {
            var index = entries.IndexOf(entry);
            if (index == entries.Length - 1)
                return entry with { ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open) };
            if (index == 0 || index > ancestorCount) return entry;
            return entry with
            {
                Receipts = entry.Receipts with
                {
                    Scribe = [receipt],
                    ChainAtoms = index == 1 && batch
                        ? [entries[0].AtomId, entries[ancestorCount + 1].AtomId]
                        : [entries[index - 1].AtomId],
                },
            };
        });
        fixture.Baseline = fixture.Document;
        return fixture;
    }

    private static void RequireValidChainBaseline(ScribeSeedFixture fixture, int ancestorCount)
    {
        var baseline = DigestStatusCommand.Run(
            fixture.Gateway(RawChangeSet.Create([ScribeSeedFixture.EntryPath(fixture.First)])),
            new FakeLeanReportSource(fixture.Inputs.Report), new FakeScribeEmissionVerifier(fixture.Verified),
            ["--base", "baseline"],
            FakeAtomHistorySource.ForPaths(fixture.Files.Keys), new DigestAgeClock());
        Assert.True(baseline.Success, baseline.Error);
        Assert.Equal(ancestorCount, baseline.Output.Split('\n').Count(line =>
            line.StartsWith("ENTRY ", StringComparison.Ordinal)
            && line.Contains("gaps=chain-migration-incomplete", StringComparison.Ordinal)));
    }

    private static void RequireProjectedChain(ScribeSeedFixture fixture, SeedExecution execution, int ancestorCount)
    {
        Assert.True(execution.Result.Success, execution.Result.Error);
        Assert.Equal(1, execution.ApplyCalls);
        var original = fixture.Document.RequireDigestionEntries();
        var affected = original.Where(entry => entry.ProjectedStatus.Truth == DigestionTruthState.Closed)
            .Select(entry => entry.AtomId).ToHashSet(StringComparer.Ordinal);
        var after = Load(execution.After).RequireDigestionEntries();
        foreach (var entry in after.Where(entry => affected.Contains(entry.AtomId)))
        {
            Assert.Equal(new DigestionStatus(DigestionMigrationState.Absorbed, DigestionTruthState.Closed),
                entry.ProjectedStatus);
            Assert.Single(entry.Receipts.Scribe);
            var before = original.Single(candidate => candidate.AtomId == entry.AtomId);
            Assert.Equal(before.Coverage.ToArray(), entry.Coverage.ToArray());
            Assert.Equal(before.Receipts.ChainAtoms.ToArray(), entry.Receipts.ChainAtoms.ToArray());
            if (!before.Receipts.Scribe.IsEmpty)
                Assert.Equal(before.Receipts.Scribe.ToArray(), entry.Receipts.Scribe.ToArray());
        }
        bool Unaffected(RawRepositoryEntry entry) => !affected.Any(id => entry.Path.EndsWith("/" + id + ".yaml", StringComparison.Ordinal));
        Assert.Equal(Image(RawRepositorySnapshot.Create(execution.Before.Entries.Where(Unaffected))),
            Image(RawRepositorySnapshot.Create(execution.After.Entries.Where(Unaffected))));
        Assert.Equal(ancestorCount, after.Count(entry => !entry.Receipts.ChainAtoms.IsEmpty));
        var validation = DigestStatusCommand.Run(new FakeRepositoryGateway(
                RawChangeSet.Create(affected.SelectMany(id => new[]
                {
                    BackfillInventoryLoader.RootPath + fixture.First.SourceId + "/partial-closed/" + id + ".yaml",
                    BackfillInventoryLoader.RootPath + fixture.First.SourceId + "/absorbed-closed/" + id + ".yaml",
                })), execution.After, execution.Before),
            new FakeLeanReportSource(fixture.Inputs.Report), new FakeScribeEmissionVerifier(fixture.Verified),
            ["--base", "baseline"],
            FakeAtomHistorySource.ForPaths(fixture.Files.Keys), new DigestAgeClock());
        Assert.True(validation.Success, validation.Error);
    }
}
