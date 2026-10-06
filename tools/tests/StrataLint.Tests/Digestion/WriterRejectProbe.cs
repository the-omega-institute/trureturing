using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class WriterRejectProbe
{
    [Fact]
    public void InstalledDecompositionRejectsMissingSelectedChildCasWithoutWrites()
    {
        const string nested = "**Theorem 1.1** First assertion.\n\n**Bundle**\n\nPreamble.\n\n- alpha\n- beta\n";
        var fixture = new DecomposeFixture(nested);
        var first = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(), fixture.Apply);
        Assert.True(first.Success, first.Error);
        var child = Assert.Single(fixture.Document.RequireDigestionEntries(), entry => entry.AtomId != fixture.Parent.AtomId
            && fixture.Snapshot.TryGetFile(DigestionCasStore.RootPath + entry.AtomId, out var blob)
            && DigestionDecompositionPolicy.IsMultiClause(DigestionAtom.FromFrozenCas(blob.RawBytes)));
        fixture.Current = RawRepositorySnapshot.Create(fixture.Current.Entries.Where(entry => entry.Path != DigestionCasStore.RootPath + child.AtomId));
        var before = fixture.Current;
        var result = DecomposeAtomCommand.Run("synthetic", fixture.Gateway, fixture.Args(child.AtomId), fixture.Apply);
        Assert.False(result.Success);
        Assert.StartsWith("DECOMPOSE_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Contains("CAS_MISSING", result.Error, StringComparison.Ordinal);
        Assert.Same(before, fixture.Current);
        Assert.Equal(1, fixture.Writes);
    }

    [Fact]
    public void InstalledSettlementRejectsStaleContextWithoutWrites()
    {
        var fixture = AtomContextFixture.Create();
        var id = AtomContextFixture.Id(fixture.Atomized.Claims[1]);
        var request = SettleAtomCommandTests.Request(fixture, id).Replace(
            "previous_atom_id = '" + AtomContextFixture.Id(fixture.Atomized.Claims[0]) + "'",
            "previous_atom_id = '" + new string('f', 64) + "'", StringComparison.Ordinal);
        var raw = fixture.RawSnapshot();
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, raw);
        var before = SettleAtomCommandTests.Image(temporary);
        var result = SettleAtomCommandTests.Run(temporary.Path, raw, request);
        Assert.False(result.Success);
        Assert.StartsWith("SETTLE_INVALID CONTEXT_MISMATCH", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
    }

    [Fact]
    public void InstalledCoverageSessionRejectsWrongFrozenStatementIdentityWithoutWrites()
    {
        var inputs = new CoverSpec().Materialize();
        var source = Assert.Single(inputs.Document.RequireDigestionSources());
        var atom = Assert.Single(source.Entries);
        var changed = atom with { Coverage = [new DigestionCoverageEdge(inputs.Gid, FrozenStatementReceiptTestData.Id('b'))] };
        var files = DirectoryLedgerTestSupport.Project(inputs.Files);
        DirectoryLedgerTestSupport.ReplaceWithProjection(files, inputs.Document.WithDigestionSources([source with { Entries = [changed] }]));
        using var temporary = new TemporaryDirectory();
        DirectoryLedgerTestSupport.Write(temporary.Path, files);
        var before = DirectoryLedgerTestSupport.Image(temporary.Path);
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), CoverWorld.Raw(files), CoverWorld.Raw(files));
        var session = new CoverAtomCommand.Session(temporary.Path, gateway, new FakeLeanReportSource(inputs.Report), CoverWorld.FixtureUtc, inputs.Gid, [atom.AtomId]);
        var result = session.Apply(atom.AtomId, [inputs.Gid]);
        Assert.False(result.Success);
        Assert.StartsWith("COVER_INVALID", result.Error, StringComparison.Ordinal);
        Assert.Contains("coverage-target-mismatch", result.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.Image(temporary.Path));
        Assert.Equal(0, gateway.WholeTreeReadCount);
    }
}
