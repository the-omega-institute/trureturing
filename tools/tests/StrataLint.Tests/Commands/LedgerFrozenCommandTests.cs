using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

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
    public void HistoricalFreezeWithoutStatePinReturnsOneAfterSourceChanges()
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: true, statePin: false);

        Assert.Equal(1, result.ExitCode);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void StatePinWithoutHistoricalFreezeReturnsZero()
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: false, statePin: true);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.Error);
    }

    [Theory]
    [InlineData("Meta/Digestion/backfill/unrelated/residual-open/" +
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.yaml")]
    [InlineData("docs/develop/theory/unrelated.md")]
    public void FrozenMembershipIgnoresUnreadableUnrelatedBody(string unrelatedPath)
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: true,
            unrelatedBody: new RawRepositoryEntry(unrelatedPath, [0xff]));

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.Error);
    }

    [Theory]
    [InlineData("Golden/Frozen/accepted/unrelated.json")]
    [InlineData("Golden/Frozen/state/D5/S0/Carrier/Other.lean.json")]
    public void FrozenMembershipStillRejectsMalformedFrozenInput(string frozenPath)
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: true,
            unrelatedBody: RawRepositoryEntry.FromText(frozenPath, "not json"));

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("LEDGER_FROZEN_INVALID", result.Error, StringComparison.Ordinal);
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

    private static ExplicitCommandResult Run(
        bool createLedgerDirectory, bool activeFreeze, bool? statePin = null,
        RawRepositoryEntry? unrelatedBody = null)
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
        entries = entries.Append(RawRepositoryEntry.FromText(
            PathFor("A"), "theorem a : True := by\n  trivial\n"));
        if (statePin ?? activeFreeze)
        {
            entries = entries.Append(RawRepositoryEntry.FromText(
                "Golden/Frozen/state/D5/S0/Carrier/A.lean.json",
                "{\"statement_id\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\"}\n"));
        }
        if (unrelatedBody is not null)
        {
            entries = entries.Append(unrelatedBody);
        }
        return LedgerFrozenCommand.Run(
            temporary.Path,
            new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create(entries), null),
            ["--target", PathFor("A")]);
    }
}
