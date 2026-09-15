using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.SettleAtomCommandTests;
using static StrataLint.Tests.UpstreamProbeVerifierTests;

namespace StrataLint.Tests;

public sealed partial class SettleUpstreamCommandTests
{
    [Theory]
    [InlineData("COVERAGE_PRESENT")]
    [InlineData("QUARANTINE_PRESENT")]
    [InlineData("DISPOSITION_PRESENT")]
    public void EarlierStateGuardsPrecedeUnresolvedSubitems(string code)
    {
        using var f = new Fixture();
        var target = f.Target with { Receipts = f.Target.Receipts with { UnresolvedSubitems = ["unresolved"] } };
        target = code switch
        {
            "COVERAGE_PRESENT" => target with { Coverage = [new("D5/S0/Carrier/Probe", null)] },
            "QUARANTINE_PRESENT" => target with { Receipts = target.Receipts with { Quarantine = new("blocked", "retry", "missing-prerequisite") } },
            "DISPOSITION_PRESENT" => target with { Receipts = target.Receipts with { CoverDisposition = new(new(DigestionMigrationState.Partial, DigestionTruthState.Closed), ["D5/S0/Carrier/Probe"], []) } },
            _ => throw new InvalidOperationException(code),
        };
        f.Context = f.Context.WithEntries([target]);
        f.ResetRaw();
        f.Reject(code);
        Assert.Empty(f.Runner.Sources);
    }

    [Fact]
    public void MalformedConflictingReceiptRemainsLoaderFailureBeforeProcess()
    {
        using var f = new Fixture();
        f.Context = f.Context.WithEntries([f.Target with { Receipts = f.Target.Receipts with
        {
            Nonpropositional = new("reason", null, null), UnresolvedSubitems = ["unresolved"],
        } }]);
        f.ResetRaw();
        f.Reject("INFRASTRUCTURE");
        Assert.Empty(f.Runner.Sources);
    }

    [Fact]
    public void CompetingCanonicalProbeIsNotOverwritten()
    {
        using var f = new Fixture();
        TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(f.Root, "Meta/Digestion/upstream"));
        TemporaryFileSystem.File.WriteAllText(Path.Combine(f.Root, f.ProbePath), "-- prior bytes\n", Encoding.UTF8);
        f.Reject("UPSTREAM_CONFLICT");
    }

    [Fact]
    public void CompanionSnapshotRacePreventsAllWrites()
    {
        using var f = new Fixture();
        f.Apply = (root, current, updates) =>
        {
            TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "Meta/Digestion/upstream"));
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, f.ProbePath), "concurrent writer\n", Encoding.UTF8);
            IngestCommand.ApplyLedgerUpdatesAtomically(root, current, updates);
        };
        var result = f.Run();
        Assert.StartsWith("SETTLE_UPSTREAM_INVALID INFRASTRUCTURE ledger companion changed under us", result.Error, StringComparison.Ordinal);
        Assert.Null(Assert.Single(BackfillInventoryLoader.LoadRoot(f.Root).RequireDigestionEntries()).Receipts.Upstream);
        Assert.Equal("concurrent writer\n", File.ReadAllText(Path.Combine(f.Root, f.ProbePath)));
    }

    [Fact]
    public void CompanionDeletionRollsBackWhenLaterWriteFails()
    {
        using var f = new Fixture();
        Assert.True(f.Run().Success);
        var before = f.LedgerImage();
        f.Apply = (root, current, updates) => IngestCommand.ApplyLedgerUpdatesAtomically(root, current,
            [.. updates.Select(update => update.Path == f.ProbePath ? update with { DurabilityOrder = int.MinValue } : update)],
            (_, _) => throw new IOException("after companion deletion"));
        Assert.False(f.Run(clear: true).Success);
        Assert.Equal(before, f.LedgerImage());
    }

    [Theory]
    [InlineData(false)]
    [InlineData(true)]
    public void CoveredAncestorsRequireAlignmentForSetAndClear(bool clear)
    {
        var context = AtomContextFixture.Create(AtomContextFixture.ListClaims, true);
        var parent = context.Ledger.RequireDigestionEntries().Single(e => !e.Receipts.ChainAtoms.IsEmpty);
        var id = parent.Receipts.ChainAtoms[1];
        context = context.WithEntries(context.Ledger.RequireDigestionEntries().Select(e => e.AtomId == parent.AtomId
            ? e with { Coverage = [new("D5/S0/Carrier/Probe", null)] } : e));
        using var f = new Fixture();
        f.Context = context;
        f.ResetRaw();
        var request = SettleAtomCommandTests.Request(context, id) + "declarations = ['True.intro']\nprobe = 'probe.lean'\n";
        var result = f.Run(request);
        Assert.True(result.Success, result.Error);
        if (clear) result = f.Run(arguments: ["--clear", id, "--base", "baseline"]);
        Assert.True(result.Success, result.Error);
        Assert.Contains("SETTLE_ALIGN_REQUIRED ancestors=" + parent.AtomId + "\n", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void UnsupportedReverifyDoesNotReadLedgerOrRunLean()
    {
        using var f = new Fixture();
        var result = f.Run(arguments: ["--reverify", "--base", "baseline"]);
        Assert.StartsWith("SETTLE_UPSTREAM_INVALID ARGUMENTS_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Empty(f.Runner.Sources);
    }
}
