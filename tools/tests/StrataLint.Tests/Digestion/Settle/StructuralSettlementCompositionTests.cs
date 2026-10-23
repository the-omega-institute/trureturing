using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.ParentSettlementTests;

namespace StrataLint.Tests;

public sealed class StructuralSettlementCompositionTests
{
    public static TheoryData<string, int, bool> Cases => new()
    {
        { "\n", 7, false }, { "\r\n", 7, false },
        { "\n", 1, false }, { "\r\n", 1, false },
        { "\n", 2, false }, { "\r\n", 2, false },
        { "\n", 4, false }, { "\r\n", 4, false },
        { "\n", 0, false }, { "\r\n", 0, false },
        { "\n", 7, true }, { "\r\n", 7, true },
        { "\n", 0, true }, { "\r\n", 0, true },
    };

    [Theory]
    [MemberData(nameof(Cases))]
    public void EmittedChildReceiptsComposeIntoParentSettlement(string newline, int gaps, bool nested)
    {
        var f = Create(newline, gaps, nested);
        var parent = Target(f);
        var preserved = f.Current.Entries.Where(entry => !entry.Path.EndsWith(".yaml", StringComparison.Ordinal)).ToArray();
        using var temporary = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(temporary.Path, f.Current);
        var descendants = f.Document.RequireDigestionEntries().Where(entry => entry.AtomId != parent.AtomId)
            .OrderBy(entry => f.Current.Entries.Single(raw => raw.Path == DigestionCasStore.RootPath + entry.AtomId).Bytes.Length)
            .Select(entry => entry.AtomId).ToArray();
        foreach (var id in descendants)
        {
            var request = EmittedRequest(f, id);
            var settled = SettleAtomCommandTests.Run(temporary.Path, f.Current, request);
            Assert.True(settled.Success, settled.Error);
            f.Current = SettleAtomCommandTests.ReadFiles(temporary);
        }
        // Children do not settle the parent implicitly; it still owes its own receipt.
        Assert.Null(Target(f).Receipts.Nonpropositional);
        var parentRequest = EmittedRequest(f, parent.AtomId);
        var before = SettleAtomCommandTests.Image(temporary);
        var wrong = SettleAtomCommandTests.Run(temporary.Path, f.Current,
            Request(parent.AtomId, parent.Receipts.ChainAtoms[0], null));
        Assert.False(wrong.Success);
        Assert.Contains("CONTEXT_MISMATCH", wrong.Error, StringComparison.Ordinal);
        Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
        var children = f.Current.Entries.Where(entry => entry.Path.EndsWith(".yaml", StringComparison.Ordinal)
            && !entry.Path.EndsWith("/" + parent.AtomId + ".yaml", StringComparison.Ordinal)).ToArray();
        var result = SettleAtomCommandTests.Run(temporary.Path, f.Current, parentRequest);
        Assert.True(result.Success, result.Error);
        f.Current = SettleAtomCommandTests.ReadFiles(temporary);
        Assert.Equal(parent.Receipts.ChainAtoms.ToArray(), Target(f).Receipts.ChainAtoms.ToArray());
        Assert.NotNull(Target(f).Receipts.Nonpropositional);
        AssertBytes(preserved.Concat(children), f.Current);
        Assert.True(SettleAtomCommandTests.Run(temporary.Path, f.Current, "", ["--clear", parent.AtomId]).Success);
        f.Current = SettleAtomCommandTests.ReadFiles(temporary);
        Assert.True(SettleAtomCommandTests.Run(temporary.Path, f.Current, "", ["--clear", descendants[0]]).Success);
        f.Current = SettleAtomCommandTests.ReadFiles(temporary);
        before = SettleAtomCommandTests.Image(temporary);
        var reopened = SettleAtomCommandTests.Run(temporary.Path, f.Current, parentRequest);
        Assert.False(reopened.Success);
        Assert.Contains("CHAIN_INCOMPLETE", reopened.Error, StringComparison.Ordinal);
        Assert.Equal(before, SettleAtomCommandTests.Image(temporary));
        AssertBytes(preserved, f.Current);
    }

    [Theory]
    [MemberData(nameof(Cases))]
    public void ScopedAndClosureConsumersAgreeOnNeighborIdentityAndBytes(string newline, int gaps, bool nested)
    {
        var f = Create(newline, gaps, nested);
        foreach (var entry in f.Document.RequireDigestionEntries())
        {
            var selected = DigestionQuerySelection.ReadContext(f.Gateway, entry.AtomId);
            var scoped = DigestionAtomContextProjection.Resolve(selected.Snapshot, selected.Document, entry.AtomId);
            var closure = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, entry.AtomId);
            AssertNeighbor(scoped.Previous, closure.Previous);
            AssertNeighbor(scoped.Current, closure.Current);
            AssertNeighbor(scoped.Next, closure.Next);
        }
        Assert.Equal(0, f.Gateway.WholeTreeReadCount);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths),
            path => path == BackfillInventoryLoader.RootPath.TrimEnd('/'));
    }

    private static DecomposeFixture Create(string newline, int gaps, bool nested)
    {
        var text = (((gaps & 1) != 0 ? "# Bundle 😀\n\n" : "")
            + "## theorem 1.1\n\nFirst assertion α.\n\n"
            + (nested ? "**Detail** Independent assertion χ.\n\n" : "")
            + ((gaps & 2) != 0 ? "# Interlude\n\n" : "")
            + "## theorem 1.2\n\nSecond assertion β.\n\n"
            + ((gaps & 4) != 0 ? "# End\n" : "")).Replace("\n", newline, StringComparison.Ordinal);
        var f = new DecomposeFixture(text, AtomizerRegistry.GenericId);
        var result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(result.Success, result.Error);
        if (nested)
        {
            var first = Target(f).Receipts.ChainAtoms[0];
            result = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(first), f.Apply);
            Assert.True(result.Success, result.Error);
        }
        return f;
    }

    private static string EmittedRequest(DecomposeFixture f, string id)
    {
        var emitted = AtomContextCommand.Run(f.Gateway, ["--atom-id", id]);
        Assert.True(emitted.Success, emitted.Error);
        return Request(id, NeighborId("PREVIOUS"), NeighborId("NEXT"));

        string? NeighborId(string label)
        {
            var line = emitted.Output.Split('\n').Single(line => line.StartsWith(label + " ", StringComparison.Ordinal));
            return line.StartsWith(label + " none ", StringComparison.Ordinal) ? null
                : line.Split(' ').Single(part => part.StartsWith("atom_id=", StringComparison.Ordinal))[8..];
        }
    }

    private static void AssertNeighbor(
        (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? scoped,
        (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? closure)
    {
        Assert.Equal(scoped?.AtomId, closure?.AtomId);
        Assert.Equal(scoped?.LedgerState, closure?.LedgerState);
        Assert.Equal(scoped?.RawBytes.ToArray(), closure?.RawBytes.ToArray());
    }

    private static void AssertBytes(IEnumerable<RawRepositoryEntry> expected, RawRepositorySnapshot actual)
    {
        foreach (var entry in expected)
            Assert.Equal(entry.Bytes.ToArray(), actual.Entries.Single(item => item.Path == entry.Path).Bytes.ToArray());
    }
}
