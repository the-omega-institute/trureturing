using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerV5CommandTests
{
    [Fact]
    public void SnapshotReplacementRemovesRevokedFreezeFiles()
    {
        using var temporary = new TemporaryDirectory();
        var files = EventFiles(BuildCatalog(Module("A"), Module("B", imports: ["A"])));
        var ledgerPath = Path.Combine(temporary.Path, "accepted");
        WriteLedgerDirectory(ledgerPath, files);

        DagLedgerAppendWriter.ReplaceEventFiles(ledgerPath, [files[1]], files);

        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath);
        Assert.Single(persisted);
        Assert.Equal(files[1].Path, persisted[0].Path);
    }
}
