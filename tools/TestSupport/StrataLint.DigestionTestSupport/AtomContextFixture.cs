using System.Collections.Immutable;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.TestSupport;

internal sealed record AtomContextFixture(
    byte[] SourceBytes,
    AtomizedTheoryDocument Atomized,
    BackfillInventoryDocument Ledger)
{
    internal DigestionContextPointerIndex? ContextIndex { get; init; }
    internal ImmutableArray<DigestionCasObject> ContextCas { get; init; } = [];
    internal const string SourcePath = "docs/source.md";
    internal const string ThreeClaims = "## Before\n\nBefore.\n\n## Middle\n\nMiddle.\n\n## After\n\nAfter.\n";
    internal const string ListClaims = "## Before\n\nBefore.\n\n## Bundle\n\n* Alpha;\n* Beta;\n* Gamma.\n\n## After\n\nAfter.\n";

    internal static AtomContextFixture Create(string text = ThreeClaims, bool expand = false)
    {
        var bytes = Encoding.UTF8.GetBytes(text);
        var atomized = AtomizerRegistry.Atomize(AtomizerRegistry.GenericId, bytes);
        var entries = atomized.Claims.Select(Entry).DistinctBy(entry => entry.AtomId).ToDictionary(static entry => entry.AtomId);
        if (expand)
        {
            foreach (var plan in atomized.ClausePlans)
            {
                var materialized = DigestionDecomposition.Materialize(entries[Id(plan.Parent)], plan, entries);
                entries[materialized.Parent.AtomId] = materialized.Parent;
                foreach (var entry in materialized.NewEntries) entries.Add(entry.AtomId, entry);
            }
        }
        var fixture = new AtomContextFixture(bytes, atomized,
            DigestionTestSupport.Document(AtomizerRegistry.GenericId,
                entries.Values.OrderByDescending(static entry => entry.AtomId, StringComparer.Ordinal).ToImmutableArray()));
        var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(DigestionTestSupport.WithSourcePolicy(fixture.RawSnapshotWithoutPointers()))).Snapshot;
        var context = DigestionContextIndexBuilder.Build(decoded, fixture.Ledger, "source", atomized);
        return fixture with { ContextIndex = context.Index, ContextCas = context.CasObjects };
    }

    internal static string Id(DigestionAtom atom) => atom.Fingerprints.RawSha256[7..];
    internal static DigestionLedgerEntry Entry(DigestionAtom atom) =>
        DigestionTestSupport.Entry(atom, Id(atom), AtomizerRegistry.GenericId);
    internal AtomContextFixture WithEntries(IEnumerable<DigestionLedgerEntry> entries) => this with
    {
        ContextIndex = null,
        ContextCas = [],
        Ledger = Ledger.WithDigestionSources([Ledger.RequireDigestionSources().Single() with
        {
            Entries = entries.ToImmutableArray(),
        }]),
    };

    internal RawRepositorySnapshot RawSnapshot(bool includeSource = true)
    {
        var snapshot = RawSnapshotWithoutPointers(includeSource);
        if (ContextIndex is null)
        {
            if (!includeSource) return snapshot;
            try
            {
                var decoded = Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(
                    DigestionTestSupport.WithSourcePolicy(snapshot))).Snapshot;
                var built = DigestionContextIndexBuilder.Build(decoded, Ledger, "source");
                return DigestionContextPointerStore.Add(RawRepositorySnapshot.Create(snapshot.Entries.Concat(
                    built.CasObjects.Where(item => !snapshot.Entries.Any(file => file.Path == item.RelativePath))
                        .Select(item => new RawRepositoryEntry(item.RelativePath, item.Bytes)))), built.Index);
            }
            catch (Exception error) when (error is FormatException or DigestionAtomContextException) { return snapshot; }
        }
        snapshot = DigestionContextPointerStore.Add(snapshot, ContextIndex);
        return RawRepositorySnapshot.Create(snapshot.Entries.Concat(ContextCas.Select(item =>
                new RawRepositoryEntry(item.RelativePath, item.Bytes)))
            .GroupBy(entry => entry.Path).Select(group => group.First()));
    }

    private RawRepositorySnapshot RawSnapshotWithoutPointers(bool includeSource = true)
    {
        var files = new List<RawRepositoryEntry>
        {
        };
        if (includeSource) files.Add(new RawRepositoryEntry(SourcePath, [.. SourceBytes]));
        var cas = new Dictionary<string, DigestionAtom>();
        var pending = new Stack<DigestionAtom>(Atomized.Claims);
        while (pending.TryPop(out var atom))
        {
            if (!cas.TryAdd(Id(atom), atom)) continue;
            if (DigestionDecomposition.PlanClauses(atom) is { } plan)
                foreach (var child in plan.Children) pending.Push(child);
        }
        files.AddRange(cas.Values.Select(atom => new RawRepositoryEntry(DigestionCasStore.RootPath + Id(atom), atom.RawBytes)));
        foreach (var source in Ledger.RequireDigestionSources())
        {
            files.Add(new RawRepositoryEntry(BackfillInventoryLoader.RootPath + source.SourceId + "/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)));
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                files.Add(new RawRepositoryEntry(
                    BackfillInventoryLoader.RootPath + source.SourceId + "/" + state + "/" + entry.AtomId + ".yaml",
                    BackfillInventoryWriter.WriteAtom(entry)));
            }
        }
        return RawRepositorySnapshot.Create(files);
    }

    internal RepositorySnapshot Snapshot(bool includeSource = true) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(DigestionTestSupport.WithSourcePolicy(RawSnapshot(includeSource)))).Snapshot;

}
