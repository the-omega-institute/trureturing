using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using Xunit;
using static StrataLint.TestSupport.AtomContextFixture;

namespace StrataLint.Tests;

public sealed class ScopedQueryAllowProbe
{
    [Fact]
    public void InstalledQueriesAllowSelectedTheoryWithUnrelatedMalformedRecords()
    {
        var fixture = Create();
        var target = Id(fixture.Atomized.Claims[1]);
        var entries = fixture.RawSnapshot().Entries.Concat(fixture.Atomized.Claims.Select(atom =>
            new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes)));
        var raw = RawRepositorySnapshot.Create(entries.Concat(new RawRepositoryEntry[]
        {
            RawRepositoryEntry.FromText("Meta/Digestion/backfill/probe-unrelated/source.toml", "invalid = ["),
            RawRepositoryEntry.FromText("Meta/Digestion/backfill/probe-unrelated/residual-open/" + new string('d', 64) + ".yaml", "invalid: ["),
        }));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), raw, null);
        var report = new FakeLeanReportSource(null);
        var environment = new ProductionCliEnvironment("/repo", gateway, report);
        var shown = environment.ShowAtom(["--atom-id", target, "--source", "source"]);
        var context = environment.AtomContext(["--atom-id", target, "--source", "source"]);
        Assert.True(shown.Success, shown.Error);
        Assert.True(context.Success, context.Error);
        Assert.Contains("Middle.", shown.Output, StringComparison.Ordinal);
        Assert.Contains("Middle.", context.Output, StringComparison.Ordinal);
        Assert.Equal(0, gateway.WholeTreeReadCount);
        Assert.Equal(0, report.CallCount);
        Assert.DoesNotContain(gateway.ScopedCurrentReads.SelectMany(scope => scope), path => path.Contains("probe-unrelated", StringComparison.Ordinal));
    }
}
