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

    [Fact]
    public void SnapshotReplacementRestoresOriginalFilesWhenPublicationFails()
    {
        using var temporary = new TemporaryDirectory();
        var files = EventFiles(BuildCatalog(Module("A"), Module("B")));
        var ledgerPath = Path.Combine(temporary.Path, "accepted");
        WriteLedgerDirectory(ledgerPath, files);
        var colliding = new RepositoryFile(
            RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/.ledger-write.lock"),
            ImmutableArray.Create<byte>(1),
            "\u0001");

        Assert.Throws<IOException>(() =>
            DagLedgerAppendWriter.ReplaceEventFiles(ledgerPath, [colliding], files));

        var persisted = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(ledgerPath)
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToArray();
        Assert.Equal(
            files.Select(static file => file.Path)
                .OrderBy(static path => path.Value, StringComparer.Ordinal),
            persisted.Select(static file => file.Path));
        Assert.All(persisted, actual => Assert.True(
            files.Single(expected => expected.Path == actual.Path)
                .RawBytes.AsSpan().SequenceEqual(actual.RawBytes.AsSpan())));
    }
}
