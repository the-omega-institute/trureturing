using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class IngestScopeTests
{
    [Fact]
    public void ReusedAtomIngestionRetainsVersionsAndRepeatsWithoutWrites()
    {
        var fixture = Fixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        File.WriteAllText(Path.Combine(temporary.Path, AlphaPath), "# Old scope\n\n" + AlphaText);
        var first = IngestLive();
        Assert.True(first.Success, first.Error);
        Assert.Contains("residual_open_added=0", first.Output, StringComparison.Ordinal);
        File.WriteAllText(Path.Combine(temporary.Path, AlphaPath), "# New scope\n\n" + AlphaText);
        var second = IngestLive();
        Assert.True(second.Success, second.Error);
        var id = Atom(AlphaText).Fingerprints.RawSha256[7..];
        var raw = DirectoryLedgerTestSupport.ReadRepository(temporary);
        Assert.Equal(2, DigestionContextPointerStore.Load(Decode(raw), "alpha", id).Length);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var third = IngestLive();
        Assert.True(third.Success, third.Error);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        File.Delete(Path.Combine(temporary.Path, AlphaPath));
        var display = AtomContextCommand.Run(new FakeRepositoryGateway(RawChangeSet.Create([]),
            DirectoryLedgerTestSupport.ReadRepository(temporary), null), ["--atom-id", id]);
        Assert.True(display.Success, display.Error);
        Assert.Contains("Old scope", display.Output, StringComparison.Ordinal);
        Assert.Contains("New scope", display.Output, StringComparison.Ordinal);

        CommandResult IngestLive() => IngestCommand.RunReportFree(temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([AlphaPath]), DirectoryLedgerTestSupport.ReadRepository(temporary), null),
            Arguments("alpha"));
    }

    [Fact]
    public void FailedContextVersionReplacementRollsBackRelationsAndNewCas()
    {
        var fixture = Fixture();
        using var temporary = new TemporaryDirectory();
        WriteFixture(temporary, fixture);
        var first = IngestCommand.RunReportFree(temporary.Path, Gateway(), Arguments("alpha"));
        Assert.True(first.Success, first.Error);
        File.WriteAllText(Path.Combine(temporary.Path, AlphaPath), "# New scope\n\n" + AlphaText);
        var before = DirectoryLedgerTestSupport.RepositoryImage(temporary);
        var called = false;
        var failed = IngestCommand.RunReportFree(temporary.Path, Gateway(), Arguments("alpha"),
            new ReportFreeIngestDependencies(CommitLedgerFile: (_, target) =>
            {
                Assert.Contains("/context/", target.Replace('\\', '/'), StringComparison.Ordinal);
                called = true;
                throw new IOException("context commit fault");
            }));
        Assert.False(failed.Success);
        Assert.True(called);
        Assert.Contains("context commit fault", failed.Error, StringComparison.Ordinal);
        Assert.Equal(before, DirectoryLedgerTestSupport.RepositoryImage(temporary));
        Assert.Empty(Directory.EnumerateFiles(temporary.Path, "*.tmp", SearchOption.AllDirectories));

        FakeRepositoryGateway Gateway() => new(RawChangeSet.Create([AlphaPath]), DirectoryLedgerTestSupport.ReadRepository(temporary), null);
    }
}
