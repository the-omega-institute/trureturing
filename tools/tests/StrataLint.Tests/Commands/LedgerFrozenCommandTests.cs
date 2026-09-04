using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.FrozenLedgerTestData;

namespace StrataLint.Tests;

public sealed class LedgerFrozenCommandTests
{
    [Fact]
    public void ActiveFreezeReturnsZeroOnTheAllowSide()
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(string.Empty, result.Output);
        Assert.Equal(string.Empty, result.Error);
    }

    [Fact]
    public void MissingActiveFreezeReturnsOne()
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: false);

        Assert.Equal(1, result.ExitCode);
    }

    [Fact]
    public void MissingLedgerDirectoryReturnsTwoAsInfrastructureFailure()
    {
        var result = Run(createLedgerDirectory: false, activeFreeze: false);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "LEDGER_FROZEN_INVALID frozen ledger is missing: Golden/Frozen/accepted",
            result.Error,
            StringComparison.Ordinal);
    }

    private static ExplicitCommandResult Run(bool createLedgerDirectory, bool activeFreeze)
    {
        using var temporary = new TemporaryDirectory();
        if (createLedgerDirectory)
        {
            Directory.CreateDirectory(Path.Combine(
                temporary.Path,
                FrozenLedgerChangeClassifier.AcceptedRoot.Replace('/', Path.DirectorySeparatorChar)));
        }

        IEnumerable<RawRepositoryEntry> entries = activeFreeze
            ? EventFiles(BuildCatalog(Module("A"))).Select(static file =>
                new RawRepositoryEntry(file.Path.Value, file.RawBytes))
            : [];
        return LedgerFrozenCommand.Run(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create(entries), null),
            ["--target", PathFor("A")]);
    }
}
