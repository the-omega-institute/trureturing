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
    public void FrozenMembershipIgnoresMalformedUnrelatedFrozenInput(string frozenPath)
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: true,
            unrelatedBody: RawRepositoryEntry.FromText(frozenPath, "not json"));

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.Error);
    }

    [Theory]
    [InlineData(false, 1)]
    [InlineData(true, 0)]
    public void FrozenMembershipDoesNotRequireTheHistoricalLedgerDirectory(bool statePin, int exitCode)
    {
        var result = Run(createLedgerDirectory: false, activeFreeze: false, statePin: statePin);

        Assert.Equal(exitCode, result.ExitCode);
        Assert.Empty(result.Error);
    }

    [Theory]
    [InlineData("not json")]
    [InlineData("{\"statement_id\":\"sha256:bad\"}\n")]
    [InlineData("{\"statement_id\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\",\"extra\":true}\n")]
    [InlineData("{ \"statement_id\":\"sha256:3333333333333333333333333333333333333333333333333333333333333333\"}\n")]
    public void FrozenMembershipRejectsMalformedTargetState(string body)
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: false,
            unrelatedBody: RawRepositoryEntry.FromText("Golden/Frozen/state/D5/S0/Carrier/A.lean.json", body));

        Assert.Equal(2, result.ExitCode);
        Assert.Contains("LEDGER_FROZEN_INVALID", result.Error, StringComparison.Ordinal);
    }

    [Theory]
    [InlineData("D5/S0/Carrier/A.txt")]
    [InlineData("D5/S0/Carrier/a.lean")]
    public void NoncanonicalModuleTargetFailsBeforeReading(string target)
    {
        using var temporary = new TemporaryDirectory();
        Directory.CreateDirectory(Path.Combine(temporary.Path, FrozenLedgerChangeClassifier.AcceptedRoot));
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create([]), null);

        var result = LedgerFrozenCommand.Run(temporary.Path, gateway, ["--target", target]);

        Assert.Equal(2, result.ExitCode);
        Assert.Equal(0, gateway.ReadCount);
    }

    [Fact]
    public void FrozenMembershipReadsOnlyTheTargetState()
    {
        var result = Run(createLedgerDirectory: true, activeFreeze: true, assertReads: gateway =>
        {
            Assert.Equal(0, gateway.WholeTreeReadCount);
            Assert.Equal([":(literal)Golden/Frozen/state/D5/S0/Carrier/A.lean.json"],
                Assert.Single(gateway.ScopedCurrentReads));
        });

        Assert.Equal(0, result.ExitCode);
    }

    private static ExplicitCommandResult Run(
        bool createLedgerDirectory, bool activeFreeze, bool? statePin = null,
        RawRepositoryEntry? unrelatedBody = null, Action<FakeRepositoryGateway>? assertReads = null)
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
        var gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), RawRepositorySnapshot.Create(entries), null);
        var result = LedgerFrozenCommand.Run(temporary.Path, gateway, ["--target", PathFor("A")]);
        assertReads?.Invoke(gateway);
        return result;
    }
}
