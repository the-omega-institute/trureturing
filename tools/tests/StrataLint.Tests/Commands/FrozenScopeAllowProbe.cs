using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.TestSupport.FrozenLedgerTestData;
using Directory = StrataLint.TestSupport.TemporaryFileSystem.Directory;

namespace StrataLint.Tests;

public sealed class FrozenScopeAllowProbe
{
    [Theory]
    [InlineData("Meta/Digestion/backfill/unrelated/residual-open/" +
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.yaml")]
    [InlineData("docs/develop/theory/unrelated.md")]
    public void UnreadableUnrelatedBodyDoesNotBlockFrozenMembership(string path)
    {
        var result = Run(true, true, unrelatedBody: new RawRepositoryEntry(path, [0xff]));
        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.Error);
    }

    [Fact]
    public void StatePinRemainsMembershipAuthorityWithoutHistoricalEvent()
    {
        var result = Run(true, false, statePin: true);
        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.Error);
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
