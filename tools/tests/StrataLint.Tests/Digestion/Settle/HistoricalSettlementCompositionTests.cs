using System.Collections.Immutable;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.ParentSettlementTests;

namespace StrataLint.Tests;

public sealed class HistoricalSettlementCompositionTests
{
    public static TheoryData<string, bool, bool> Cases => new()
    {
        { "\n", false, false }, { "\r\n", false, false },
        { "\n", true, false }, { "\r\n", true, false },
        { "\n", false, true }, { "\r\n", false, true },
        { "\n", true, true }, { "\r\n", true, true },
    };

    [Theory]
    [MemberData(nameof(Cases))]
    public void ScopedAndClosureNeighborsKeepSupportedStoredBoundaries(string newline, bool nested, bool proseCut)
    {
        var f = Create(newline, nested, proseCut);
        foreach (var entry in f.Document.RequireDigestionEntries())
        {
            var selected = DigestionQuerySelection.ReadContext(f.Gateway, entry.AtomId);
            var a = DigestionAtomContextProjection.Resolve(selected.Snapshot, selected.Document, entry.AtomId);
            var b = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, entry.AtomId);
            Same(a.Previous, b.Previous);
            Same(a.Current, b.Current);
            Same(a.Next, b.Next);
        }
        Assert.Equal(0, f.Gateway.WholeTreeReadCount);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths),
            path => path == BackfillInventoryLoader.RootPath.TrimEnd('/'));
    }

    [Theory]
    [MemberData(nameof(Cases))]
    public void EmittedHistoricalChildReceiptsComposeWithIndependentParentReceipt(string newline, bool nested, bool proseCut)
    {
        var f = Create(newline, nested, proseCut);
        var parent = Target(f);
        var immutable = f.Current.Entries.Where(e => !e.Path.EndsWith(".yaml", StringComparison.Ordinal)).ToArray();
        using var dir = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(dir.Path, f.Current);
        var descendants = DigestionDecomposition.ValidatedClosure([parent.AtomId],
            f.Document.RequireDigestionEntries().ToDictionary(e => e.AtomId), f.Snapshot);
        descendants.Remove(parent.AtomId);
        foreach (var id in descendants.OrderBy(id => f.Current.Entries.Single(e => e.Path == DigestionCasStore.RootPath + id).Bytes.Length))
        {
            var result = SettleAtomCommandTests.Run(dir.Path, f.Current, Emitted(f, id));
            Assert.True(result.Success, result.Error);
            f.Current = SettleAtomCommandTests.ReadFiles(dir);
        }
        Assert.Null(Target(f).Receipts.Nonpropositional);
        var request = Emitted(f, parent.AtomId);
        var image = SettleAtomCommandTests.Image(dir);
        var wrong = SettleAtomCommandTests.Run(dir.Path, f.Current, Request(parent.AtomId, parent.Receipts.ChainAtoms[0], null));
        Assert.False(wrong.Success);
        Assert.Contains("CONTEXT_MISMATCH", wrong.Error, StringComparison.Ordinal);
        Assert.Equal(image, SettleAtomCommandTests.Image(dir));
        var childBytes = f.Current.Entries.Where(e => e.Path.EndsWith(".yaml", StringComparison.Ordinal)).ToArray();
        var settled = SettleAtomCommandTests.Run(dir.Path, f.Current, request);
        Assert.True(settled.Success, settled.Error);
        f.Current = SettleAtomCommandTests.ReadFiles(dir);
        Assert.NotNull(Target(f).Receipts.Nonpropositional);
        Assert.Equal(parent.Receipts.ChainAtoms.ToArray(), Target(f).Receipts.ChainAtoms.ToArray());
        Bytes(immutable.Concat(childBytes.Where(e => !e.Path.EndsWith("/" + parent.AtomId + ".yaml", StringComparison.Ordinal))), f.Current);
        Assert.True(SettleAtomCommandTests.Run(dir.Path, f.Current, "", ["--clear", parent.AtomId]).Success);
        f.Current = SettleAtomCommandTests.ReadFiles(dir);
        Assert.True(SettleAtomCommandTests.Run(dir.Path, f.Current, "", ["--clear", parent.Receipts.ChainAtoms[^1]]).Success);
        f.Current = SettleAtomCommandTests.ReadFiles(dir);
        image = SettleAtomCommandTests.Image(dir);
        var reopened = SettleAtomCommandTests.Run(dir.Path, f.Current, request);
        Assert.False(reopened.Success);
        Assert.Contains("CHAIN_INCOMPLETE", reopened.Error, StringComparison.Ordinal);
        Assert.Equal(image, SettleAtomCommandTests.Image(dir));
        Bytes(immutable, f.Current);
    }

    private static DecomposeFixture Create(string newline, bool nested, bool proseCut)
    {
        string N(string s) => s.Replace("\n", newline, StringComparison.Ordinal);
        var pieces = proseCut
            ? new[] { N("# Bundle 😀\n\n## theorem 1.1\n\nFirst α "), N("continues χ.\n\n# Interlude\n\n## theorem 1.2\n\nSecond β.\n\n# End\n") }
            : new[] { N("# Bundle 😀\n\n## theorem 1.1\n\nFirst α.\n\n# Interlude\n\n"), N("## theorem 1.2\n\nSecond β.\n\n# End\n") };
        var f = new DecomposeFixture(string.Concat(pieces), AtomizerRegistry.GenericId);
        AddChain(f, f.Parent, pieces);
        if (nested)
        {
            var first = pieces[0];
            var cut = first.IndexOf("First", StringComparison.Ordinal);
            AddChain(f, DecomposeFixture.Entry(first, AtomizerRegistry.GenericId), [first[..cut], first[cut..]]);
        }
        var before = f.Current;
        var replay = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(replay.Success, replay.Error);
        Assert.Same(before, f.Current);
        Assert.Equal(0, f.Writes);
        var plan = DigestionDecomposition.Plan(Target(f),
            f.Current.Entries.Single(e => e.Path == DigestionCasStore.RootPath + f.Parent.AtomId).Bytes,
            GenericAtomizer.Atomize, f.Snapshot);
        Assert.Null(DigestionDecomposition.IntegrityFailure(plan));
        return f;
    }

    private static void AddChain(DecomposeFixture f, DigestionLedgerEntry parent, string[] parts)
    {
        foreach (var part in parts) f.Add(DecomposeFixture.Entry(part, AtomizerRegistry.GenericId), part);
        f.Replace(parent with { Receipts = parent.Receipts with
        { ChainAtoms = [.. parts.Select(s => DecomposeFixture.Entry(s, AtomizerRegistry.GenericId).AtomId)] } });
    }

    private static string Emitted(DecomposeFixture f, string id)
    {
        var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", id]);
        Assert.True(result.Success, result.Error);
        return Request(id, Neighbor("PREVIOUS"), Neighbor("NEXT"));
        string? Neighbor(string label)
        {
            var line = result.Output.Split('\n').Single(l => l.StartsWith(label + " ", StringComparison.Ordinal));
            return line.StartsWith(label + " none ", StringComparison.Ordinal) ? null
                : line.Split(' ').Single(p => p.StartsWith("atom_id=", StringComparison.Ordinal))[8..];
        }
    }

    private static void Same((string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? a,
        (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? b)
    {
        Assert.Equal(a?.AtomId, b?.AtomId);
        Assert.Equal(a?.RawBytes.ToArray(), b?.RawBytes.ToArray());
    }

    private static void Bytes(IEnumerable<RawRepositoryEntry> expected, RawRepositorySnapshot actual)
    {
        foreach (var e in expected) Assert.Equal(e.Bytes.ToArray(), actual.Entries.Single(a => a.Path == e.Path).Bytes.ToArray());
    }
}
