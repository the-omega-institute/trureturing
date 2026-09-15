using System.Collections.Immutable;
using System.Globalization;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using File = StrataLint.TestSupport.TemporaryFileSystem.File;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

public sealed class ReconcileChainTests
{
    private const string First = "## theorem 1: Synthetic regroup\n\nFirst assertion α.\n\n";
    private const string Second = "Second assertion β. ";
    private const string Third = "Third assertion γ. ";
    private const string Last = "Independent assertion δ.\n\n";
    private const string Group = First + Second + Third;

    [Fact]
    public void LegalExplicitRegroupWritesOnlyParentAndPreservesEveryDescendant()
    {
        var f = Flat();
        // A group is first materialized by the ordinary owner, using explicit byte cuts.
        var nested = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            [.. f.Args(Id(Group)), "--split-at", Count(First), "--split-at", Count(First + Second)], f.Apply);
        Assert.True(nested.Success, nested.Error);
        Assert.Equal(new[] { Id(First), Id(Second), Id(Third) }, Entry(f, Group).Receipts.ChainAtoms);
        var before = f.Current;
        var dryRun = DecomposeAtomCommand.Run("synthetic", f.Gateway, [.. Regroup(f), "--dry-run"], f.Apply);
        Assert.True(dryRun.Success, dryRun.Error);
        Assert.Contains("cas_objects=0 ledger_updates=1", dryRun.Output, StringComparison.Ordinal);
        Assert.Same(before, f.Current);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, Regroup(f), f.Apply);
        Assert.True(result.Success, result.Error);
        Assert.Equal(new[] { Id(Group), Id(Last) }, Entry(f, Group + Last).Receipts.ChainAtoms);
        Assert.Empty(f.CasWrites);
        Assert.Single(f.LedgerWrites);
        Assert.Equal(DecomposeFixture.PathFor(f.Parent), f.LedgerWrites[0].Path);
        foreach (var prior in before.Entries.Where(e => e.Path != DecomposeFixture.PathFor(f.Parent)))
            Assert.Equal(prior.Bytes.ToArray(), f.Current.Entries.Single(e => e.Path == prior.Path).Bytes.ToArray());
        Assert.All(new[] { Entry(f, Group), Entry(f, Group + Last) }, e =>
            Assert.Equal(new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open), e.ProjectedStatus));
        var alignment = DigestionLedgerAligner.Evaluate(f.Document, f.Snapshot, f.Document, DigestionAlignmentMode.Ingest);
        Assert.Empty(alignment.Findings);
        Assert.Contains(Id(Group), alignment.VerifiedClausePlanParents);
        Assert.Contains(f.Parent.AtomId, alignment.VerifiedClausePlanParents);
        var context = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, Id(Third));
        Assert.Equal(Id(Second), context.Previous!.Value.AtomId);
        Assert.Equal(Id(Last), context.Next!.Value.AtomId);
        Assert.Equal(4, context.Count);
        var repeated = f.Current;
        Assert.True(DecomposeAtomCommand.Run("synthetic", f.Gateway, Regroup(f), f.Apply).Success);
        Assert.Same(repeated, f.Current);
    }

    [Fact]
    public void RegisteredProductionDispatchNeedsNeitherLeanNorScribe()
    {
        var f = Ready();
        var lean = new FakeLeanReportSource(null);
        var scribe = new FakeScribeEmissionVerifier(null);
        var environment = new ProductionCliEnvironment("synthetic", f.Gateway, lean, scribe);
        var console = new BufferedConsole();
        var before = f.Current;
        Assert.Equal(0, CliApplication.Run(["decompose-atom", .. Regroup(f), "--dry-run"], environment, console));
        Assert.Contains("reconcile_chain=true", console.Output, StringComparison.Ordinal);
        Assert.Equal(0, lean.CallCount);
        Assert.Equal(0, scribe.CallCount);
        Assert.Same(before, f.Current);
        var rejected = new BufferedConsole();
        Assert.Equal(2, CliApplication.Run(["decompose-atom", .. f.Args(), "--split-at", Count(Group), "--dry-run"], environment, rejected));
        Assert.Contains("CHAIN_CONFLICT", rejected.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void OrdinaryGuardRejectsRegroupAndExplicitModeStillHonorsCanonicalPlan()
    {
        var f = Ready();
        Reject(f, [.. f.Args(), "--split-at", Count(Group)], "CHAIN_CONFLICT");
        var marked = new DecomposeFixture();
        Assert.True(DecomposeAtomCommand.Run("synthetic", marked.Gateway, marked.Args(), marked.Apply).Success);
        Reject(marked, [.. marked.Args(), "--reconcile-chain", "--split-at", "10"], "PLAN_CONFLICT");
        var empty = new DecomposeFixture();
        Reject(empty, [.. empty.Args(), "--reconcile-chain"], "CHAIN_RECONCILE_REQUIRES_EXISTING_CHAIN");
    }

    [Theory]
    [InlineData("coverage", "CHAIN_RECONCILE_LIVE_OBLIGATIONS")]
    [InlineData("unresolved", "CHAIN_RECONCILE_LIVE_OBLIGATIONS")]
    [InlineData("tail", "CHAIN_RECONCILE_LIVE_OBLIGATIONS")]
    [InlineData("quarantine", "QUARANTINED")]
    [InlineData("disposition", "CHAIN_RECONCILE_LIVE_OBLIGATIONS")]
    [InlineData("nonpropositional", "CHAIN_RECONCILE_LIVE_OBLIGATIONS")]
    public void LiveParentObligationsFailWithoutAnyWrite(string kind, string code)
    {
        var f = Ready();
        var parent = Entry(f, Group + Last);
        var receipts = parent.Receipts;
        parent = kind switch
        {
            "coverage" => parent with { Coverage = [new DigestionCoverageEdge("D5/S0/Carrier/Probe.probe", null)] },
            "unresolved" => parent with { Receipts = receipts with { UnresolvedSubitems = ["independent obligation"] } },
            "tail" => parent with { Receipts = receipts with { TailAuthorization = new("tools/Authorizations/digestion-tail/" + parent.AtomId + ".json", "sha256:" + new string('a', 64)) } },
            "quarantine" => parent with { Receipts = receipts with { Quarantine = new("blocked", "supply witness", "missing-prerequisite") } },
            "disposition" => parent with { Receipts = receipts with { CoverDisposition = new(parent.ProjectedStatus, ["D5/S0/Carrier/Probe.probe"], [new("target-open", "synthetic")]) } },
            "nonpropositional" => parent with { Receipts = receipts with { Nonpropositional = new("synthetic fixture receipt", null, null) } },
            _ => throw new ArgumentException(kind),
        };
        f.Replace(parent);
        Reject(f, Regroup(f), code);
        // A flag with an unchanged plan must not erase unresolved receipts either.
        if (kind == "unresolved") Reject(f, [.. f.Args(), "--reconcile-chain"], code);
    }

    [Fact]
    public void ChildDropFailsEvenWhenProposedGroupHasIdenticalCombinedBytes()
    {
        var f = Flat(); // Group exists but has no child chain: byte equality is insufficient.
        Reject(f, Regroup(f), "CHAIN_RECONCILE_DROPS_CHILD");
    }

    [Theory]
    [InlineData("missing", "CHILD_MISSING")]
    [InlineData("cas-missing", "CHILD_CAS_MISSING")]
    [InlineData("cas-corrupt", "CHILD_CAS_MISMATCH")]
    [InlineData("normalized", "CHILD_IDENTITY_CONFLICT")]
    [InlineData("cycle", "clause plan children exceed parent bytes")]
    [InlineData("reversed", "differs from its parent span")]
    public void NestedIdentityAndChainDefectsFailClosed(string defect, string code)
    {
        var f = Ready();
        var child = Entry(f, Second);
        if (defect == "missing")
            f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(e => e.Path != DecomposeFixture.PathFor(child)));
        if (defect is "cas-missing" or "cas-corrupt")
            f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(e => e.Path != DigestionCasStore.RootPath + child.AtomId)
                .Concat(defect == "cas-corrupt" ? new[] { RawRepositoryEntry.FromText(DigestionCasStore.RootPath + child.AtomId, "changed") } : []));
        if (defect == "normalized")
            f.Replace(child with { Fingerprints = child.Fingerprints with { NormalizedSha256 = "sha256:" + new string('b', 64) } });
        if (defect == "cycle")
            f.Replace(child with { Receipts = child.Receipts with { ChainAtoms = [Id(Group)] } });
        if (defect == "reversed")
        {
            var group = Entry(f, Group);
            f.Replace(group with { Receipts = group.Receipts with { ChainAtoms = [Id(Third), Id(Second), Id(First)] } });
        }
        Reject(f, Regroup(f), code);
    }

    [Fact]
    public void ProductionWriterCommitsRegroupToPrivateDisk()
    {
        var f = Ready();
        using var disk = new TemporaryDirectory();
        Write(disk, f.Current);
        var lean = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment(disk.Path, f.Gateway, lean, new FakeScribeEmissionVerifier(null));
        Assert.Equal(0, CliApplication.Run(["decompose-atom", .. Regroup(f)], environment, new BufferedConsole()));
        var actual = DirectoryLedgerTestSupport.ReadRepository(disk);
        var document = BackfillInventoryLoader.Load(DecomposeFixture.Decode(actual));
        Assert.Equal(new[] { Id(Group), Id(Last) }, document.RequireDigestionEntries().Single(e => e.AtomId == f.Parent.AtomId).Receipts.ChainAtoms);
        foreach (var prior in f.Current.Entries.Where(e => e.Path != DecomposeFixture.PathFor(f.Parent)))
            Assert.Equal(prior.Bytes.ToArray(), actual.Entries.Single(e => e.Path == prior.Path).Bytes.ToArray());
        Assert.Equal(0, lean.CallCount);
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void RealAtomicWriterRollsBackLedgerAndOnlyNewCas(bool reconcile)
    {
        var f = reconcile ? Ready() : new DecomposeFixture();
        if (!reconcile) f.Add(DecomposeFixture.Entry("**Second** Second assertion.\n"), "**Second** Second assertion.\n");
        using var disk = new TemporaryDirectory();
        Write(disk, f.Current);
        var before = DirectoryLedgerTestSupport.RepositoryImage(disk);
        var staged = false;
        var committed = 0;
        var result = DecomposeAtomCommand.Run(disk.Path, f.Gateway, reconcile ? Regroup(f) : f.Args(),
            (root, current, cas, updates) =>
            {
                Assert.Equal(reconcile ? 0 : 1, cas.Length);
                IngestCommand.ApplyDecompositionAtomically(root, current, cas, updates, (pending, target) =>
                {
                    Assert.All(cas, item => Assert.Equal(item.Bytes.ToArray(), File.ReadAllBytes(Path.Combine(root, item.RelativePath))));
                    staged = true;
                    // Replace an actual ledger shard before throwing, exercising restoration as well as cleanup.
                    System.IO.File.Move(pending, target, overwrite: true);
                    committed++;
                    throw new IOException("injected after ledger replacement");
                });
            });
        Assert.False(result.Success);
        Assert.Contains("injected after ledger replacement", result.Error, StringComparison.Ordinal);
        Assert.Empty(result.Output);
        Assert.True(staged);
        Assert.Equal(1, committed);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(disk));
        Assert.DoesNotContain(Directory.EnumerateFiles(disk.Path, "*", SearchOption.AllDirectories), path => path.EndsWith(".tmp", StringComparison.Ordinal));
    }

    private static DecomposeFixture Flat()
    {
        var f = new DecomposeFixture(Group + Last, AtomizerRegistry.GenericId);
        foreach (var text in new[] { First, Second, Third, Last, Group }) f.Add(DecomposeFixture.Entry(text, AtomizerRegistry.GenericId), text);
        var first = Entry(f, First);
        f.Replace(first with
        {
            Coverage = [new DigestionCoverageEdge("D5/S0/Carrier/Probe.first", null)],
            ProjectedStatus = new(DigestionMigrationState.Partial, DigestionTruthState.Open),
        });
        var second = Entry(f, Second);
        f.Replace(second with { Receipts = second.Receipts with { UnresolvedSubitems = ["retained child obligation"] } });
        f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [Id(First), Id(Second), Id(Third), Id(Last)] } });
        return f;
    }

    private static DecomposeFixture Ready()
    {
        var f = Flat();
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway,
            [.. f.Args(Id(Group)), "--split-at", Count(First), "--split-at", Count(First + Second)], f.Apply);
        Assert.True(result.Success, result.Error);
        return f;
    }

    private static string Id(string text) => DecomposeFixture.Entry(text, AtomizerRegistry.GenericId).AtomId;
    private static string Count(string text) => Encoding.UTF8.GetByteCount(text).ToString(CultureInfo.InvariantCulture);
    private static DigestionLedgerEntry Entry(DecomposeFixture f, string text) => f.Document.RequireDigestionEntries().Single(e => e.AtomId == Id(text));
    private static string[] Regroup(DecomposeFixture f) => [.. f.Args(), "--reconcile-chain", "--split-at", Count(Group)];

    private static void Reject(DecomposeFixture f, string[] args, string code)
    {
        var before = f.Current;
        var writes = f.Writes;
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, args, f.Apply);
        Assert.False(result.Success);
        Assert.Contains(code, result.Error, StringComparison.Ordinal);
        Assert.Empty(result.Output);
        Assert.Same(before, f.Current);
        Assert.Equal(writes, f.Writes);
    }

    private static void Write(TemporaryDirectory disk, RawRepositorySnapshot snapshot)
    {
        foreach (var entry in snapshot.Entries)
        {
            var path = Path.Combine(disk.Path, entry.Path);
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.ToArray());
        }
    }
}
