using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using static StrataLint.Tests.ParentSettlementTests;

namespace StrataLint.Tests;

public sealed class HistoricalReferenceOwnershipTests
{
    public static IEnumerable<object[]> Cases =>
        from newline in new[] { "\n", "\r\n" }
        from foreignParent in new[] { false, true }
        from owners in Enumerable.Range(0, 4)
        from nested in new[] { false, true }
        select new object[] { newline, foreignParent, owners, nested };

    [Theory]
    [MemberData(nameof(Cases))]
    public void OwningSourceContextComposesAcrossHistoricalReferenceOwners(
        string newline, bool foreignParent, int owners, bool nested)
    {
        var f = Create(newline, foreignParent, owners, nested);
        var parent = Target(f);
        var original = f.Current;
        var closure = DigestionDecomposition.ValidatedClosure([parent.AtomId],
            f.Document.RequireDigestionEntries().ToDictionary(e => e.AtomId), f.Snapshot);
        Assert.Equal(nested ? 7 : 3, closure.Count);
        var replay = DecomposeAtomCommand.Run("synthetic", f.Gateway, f.Args(), f.Apply);
        Assert.True(replay.Success, replay.Error);
        Assert.Same(original, f.Current);
        Assert.Equal(0, f.Writes);
        foreach (var entry in f.Document.RequireDigestionEntries())
        {
            var selected = DigestionQuerySelection.ReadContext(f.Gateway, entry.AtomId);
            var scoped = DigestionAtomContextProjection.Resolve(selected.Snapshot, selected.Document, entry.AtomId);
            var full = DigestionAtomContextProjection.Resolve(f.Snapshot, f.Document, entry.AtomId);
            Same(scoped.Previous, full.Previous);
            Same(scoped.Current, full.Current);
            Same(scoped.Next, full.Next);
        }
        Assert.Equal(0, f.Gateway.WholeTreeReadCount);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths), path =>
            path == BackfillInventoryLoader.RootPath.TrimEnd('/') || path == DigestionCasStore.RootPath.TrimEnd('/'));
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths), path => path.Contains("unrelated", StringComparison.Ordinal));
        using var dir = new TemporaryDirectory();
        SettleAtomCommandTests.WriteFiles(dir.Path, f.Current);
        foreach (var id in closure.Where(id => id != parent.AtomId).OrderBy(id =>
            f.Current.Entries.Single(e => e.Path == DigestionCasStore.RootPath + id).Bytes.Length))
        {
            var result = SettleAtomCommandTests.Run(dir.Path, f.Current, Emitted(f, id));
            Assert.True(result.Success, result.Error);
            f.Current = SettleAtomCommandTests.ReadFiles(dir);
        }
        Assert.Null(Target(f).Receipts.Nonpropositional);
        var request = Emitted(f, parent.AtomId);
        var image = SettleAtomCommandTests.Image(dir);
        var wrong = SettleAtomCommandTests.Run(dir.Path, f.Current,
            Request(parent.AtomId, parent.Receipts.ChainAtoms[0], null));
        Assert.False(wrong.Success);
        Assert.Contains("CONTEXT_MISMATCH", wrong.Error, StringComparison.Ordinal);
        Assert.Equal(image, SettleAtomCommandTests.Image(dir));
        var children = f.Current;
        var settled = SettleAtomCommandTests.Run(dir.Path, f.Current, request);
        Assert.True(settled.Success, settled.Error);
        f.Current = SettleAtomCommandTests.ReadFiles(dir);
        Assert.NotNull(Target(f).Receipts.Nonpropositional);
        Assert.Equal(parent.Receipts.ChainAtoms.ToArray(), Target(f).Receipts.ChainAtoms.ToArray());
        Preserved(children.Entries.Where(e => !e.Path.EndsWith("/" + parent.AtomId + ".yaml", StringComparison.Ordinal)), f.Current);
        image = SettleAtomCommandTests.Image(dir);
        var replaySettle = SettleAtomCommandTests.Run(dir.Path, f.Current, request);
        Assert.False(replaySettle.Success);
        Assert.Contains("NOT_RESIDUAL_OPEN", replaySettle.Error, StringComparison.Ordinal);
        Assert.Equal(image, SettleAtomCommandTests.Image(dir));
        Assert.True(SettleAtomCommandTests.Run(dir.Path, f.Current, "", ["--clear", parent.AtomId]).Success);
        f.Current = SettleAtomCommandTests.ReadFiles(dir);
        var intact = f.Current;
        foreach (var fault in new[] { "cas", "chain" })
        {
            f.Current = intact;
            if (fault == "chain") f.Replace(Target(f) with { Receipts = Target(f).Receipts with
                { ChainAtoms = parent.Receipts.ChainAtoms.Reverse().ToImmutableArray() } });
            else
            {
                var path = fault == "source" ? parent.SourcePath : DigestionCasStore.RootPath + parent.Receipts.ChainAtoms[0];
                f.Current = RawRepositorySnapshot.Create(intact.Entries.Select(e => e.Path == path
                    ? RawRepositoryEntry.FromText(path, "Changed bytes Ω.\n") : e));
            }
            image = SettleAtomCommandTests.Image(dir);
            var rejected = SettleAtomCommandTests.Run(dir.Path, f.Current, request);
            Assert.False(rejected.Success);
            Assert.Equal(image, SettleAtomCommandTests.Image(dir));
        }
        f.Current = intact;
        Assert.True(SettleAtomCommandTests.Run(dir.Path, f.Current, "", ["--clear", parent.Receipts.ChainAtoms[0]]).Success);
        f.Current = SettleAtomCommandTests.ReadFiles(dir);
        image = SettleAtomCommandTests.Image(dir);
        var reopened = SettleAtomCommandTests.Run(dir.Path, f.Current, request);
        Assert.False(reopened.Success);
        Assert.Contains("CHAIN_INCOMPLETE", reopened.Error, StringComparison.Ordinal);
        Assert.Equal(image, SettleAtomCommandTests.Image(dir));
        Preserved(original.Entries.Where(e => !e.Path.EndsWith(".yaml", StringComparison.Ordinal)), f.Current);

    }

    [Fact]
    public void IncidentalForeignChainDoesNotBecomeARootOfTheOwningSourceFallback()
    {
        const string first = "## theorem 1.1\n\n";
        const string second = "## theorem 1.2\n\n";
        var f = new DecomposeFixture(first + second, AtomizerRegistry.GenericId);
        var source = f.Document.RequireDigestionSources().Single();
        var left = DecomposeFixture.Entry(first, AtomizerRegistry.GenericId);
        var right = DecomposeFixture.Entry(second, AtomizerRegistry.GenericId);
        f.Add(left, first);
        f.Add(right, second);
        const string prefix = "## theorem ";
        var fragments = new[] { prefix, second[prefix.Length..] };
        foreach (var fragment in fragments)
            f.Add(DecomposeFixture.Entry(fragment, AtomizerRegistry.GenericId), fragment);
        f.Replace(f.Parent with { Receipts = f.Parent.Receipts with { ChainAtoms = [left.AtomId, right.AtomId] } });
        f.Replace(right with { Receipts = right.Receipts with
            { ChainAtoms = [.. fragments.Select(fragment => DecomposeFixture.Entry(fragment, AtomizerRegistry.GenericId).AtomId)] } });
        foreach (var entry in f.Document.RequireDigestionEntries().Where(entry => entry.AtomId != left.AtomId).ToArray())
            f.Replace(entry with { SourceId = "foreign", SourcePath = "docs/foreign.md" });
        var foreign = source with { SourceId = "foreign", SourcePath = "docs/foreign.md" };
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Concat(new[]
        {
            new RawRepositoryEntry(BackfillInventoryLoader.RootPath + "foreign/source.toml", BackfillInventoryWriter.WriteSourceMetadata(foreign)),
            RawRepositoryEntry.FromText(foreign.SourcePath, first + second),
            RawRepositoryEntry.FromText(BackfillInventoryLoader.RootPath + "unrelated/residual-open/" + new string('f', 64) + ".yaml", "broken: ["),
        }));
        f.Current = DigestionTestSupport.WithSourcePolicy(RawRepositorySnapshot.Create(
            f.Current.Entries.Where(entry => entry.Path != FileMapLoader.RelativePath)));
        var unrelated = f.Current.Entries.Single(entry => entry.Path.Contains("unrelated", StringComparison.Ordinal));
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Where(entry => entry != unrelated));
        f.CaptureContext();
        f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Append(unrelated));
        var query = DigestionQuerySelection.ReadContext(f.Gateway, left.AtomId);
        var scoped = DigestionAtomContextProjection.Resolve(query.Snapshot, query.Document, left.AtomId);
        Assert.DoesNotContain(f.Gateway.ScopedCurrentReads.SelectMany(paths => paths),
            path => path.Contains("unrelated", StringComparison.Ordinal));
        var complete = RawRepositorySnapshot.Create(f.Current.Entries.Where(entry => !entry.Path.Contains("unrelated", StringComparison.Ordinal)));
        var snapshot = DecomposeFixture.Decode(complete);
        var document = BackfillInventoryLoader.Load(snapshot);
        Assert.Empty(GenericAtomizer.Atomize(Encoding.UTF8.GetBytes(first + second)).Claims);
        Assert.Equal(5, DigestionDecomposition.ValidatedClosure([f.Parent.AtomId],
            document.RequireDigestionEntries().ToDictionary(entry => entry.AtomId), snapshot).Count);
        var closure = DigestionAtomContextProjection.Resolve(snapshot, document, left.AtomId);
        Same(scoped.Previous, closure.Previous);
        Same(scoped.Current, closure.Current);
        Same(scoped.Next, closure.Next);
    }

    private static DecomposeFixture Create(string newline, bool foreignParent, int owners, bool nested)
    {
        string N(string value) => value.Replace("\n", newline, StringComparison.Ordinal);
        var parts = new[] { N("# Bundle 😀\n\n## theorem 1.1\n\nFirst α with é.\n\n# Interlude Ω\n\n"),
            N("## theorem 1.2\n\nSecond β.\n\n# End λ\n") };
        var text = string.Concat(parts);
        var f = new DecomposeFixture(text, AtomizerRegistry.GenericId);
        AddChain(f.Parent, parts);
        if (nested)
            foreach (var part in parts)
            {
                var cut = part.IndexOf(part == parts[0] ? "First" : "Second", StringComparison.Ordinal);
                AddChain(DecomposeFixture.Entry(part, AtomizerRegistry.GenericId), [part[..cut], part[cut..]]);
            }
        var source = f.Document.RequireDigestionSources().Single();
        foreach (var entry in f.Document.RequireDigestionEntries())
        {
            var owner = entry.AtomId == f.Parent.AtomId ? (foreignParent ? "root" : "probe")
                : (owners & (parts[0].Contains(Raw(entry), StringComparison.Ordinal) ? 1 : 2)) != 0
                    ? (parts[0].Contains(Raw(entry), StringComparison.Ordinal) ? "left" : "right") : "probe";
            if (owner != "probe") f.Replace(entry with { SourceId = owner, SourcePath = "docs/" + owner + ".md" });
        }
        foreach (var owner in new[] { "root", "left", "right" })
        {
            var foreign = source with { SourceId = owner, SourcePath = "docs/" + owner + ".md" };
            f.Current = RawRepositorySnapshot.Create(f.Current.Entries.Concat(new[]
            {
                new RawRepositoryEntry(BackfillInventoryLoader.RootPath + owner + "/source.toml", BackfillInventoryWriter.WriteSourceMetadata(foreign)),
                RawRepositoryEntry.FromText(foreign.SourcePath, text),
            }));
        }
        f.Current = DigestionTestSupport.WithSourcePolicy(RawRepositorySnapshot.Create(
            f.Current.Entries.Where(entry => entry.Path != FileMapLoader.RelativePath)));
        f.CaptureContext();
        return f;

        string Raw(DigestionLedgerEntry entry) => Encoding.UTF8.GetString(f.Current.Entries.Single(e =>
            e.Path == DigestionCasStore.RootPath + entry.AtomId).Bytes.AsSpan());
        void AddChain(DigestionLedgerEntry parent, string[] chunks)
        {
            foreach (var chunk in chunks) f.Add(DecomposeFixture.Entry(chunk, AtomizerRegistry.GenericId), chunk);
            f.Replace(parent with { Receipts = parent.Receipts with
                { ChainAtoms = [.. chunks.Select(chunk => DecomposeFixture.Entry(chunk, AtomizerRegistry.GenericId).AtomId)] } });
        }
    }

    private static string Emitted(DecomposeFixture f, string id)
    {
        var result = AtomContextCommand.Run(f.Gateway, ["--atom-id", id]);
        Assert.True(result.Success, result.Error);
        return Request(id, Neighbor("PREVIOUS"), Neighbor("NEXT"));
        string? Neighbor(string label)
        {
            var line = result.Output.Split('\n').Single(line => line.StartsWith(label + " ", StringComparison.Ordinal));
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

    private static void Preserved(IEnumerable<RawRepositoryEntry> expected, RawRepositorySnapshot actual)
    {
        foreach (var entry in expected)
            Assert.Equal(entry.Bytes.ToArray(), actual.Entries.Single(e => e.Path == entry.Path).Bytes.ToArray());
    }
}
