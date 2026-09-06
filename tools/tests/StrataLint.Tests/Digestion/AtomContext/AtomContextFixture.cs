using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed record AtomContextFixture(
    byte[] SourceBytes,
    AtomizedTheoryDocument Atomized,
    BackfillInventoryDocument Ledger)
{
    internal const string SourcePath = "docs/source.md";
    internal const string ThreeClaims = "## Before\n\nBefore.\n\n## Middle\n\nMiddle.\n\n## After\n\nAfter.\n";
    internal const string ListClaims = "## Before\n\nBefore.\n\n## Bundle\n\n* Alpha;\n* Beta;\n* Gamma.\n\n## After\n\nAfter.\n";

    internal static AtomContextFixture Create(string text = ThreeClaims, bool expand = false)
    {
        var bytes = Encoding.UTF8.GetBytes(text);
        var atomized = AtomizerRegistry.Atomize(AtomizerRegistry.GenericId, bytes, DigestionTestSupport.Rules);
        var entries = atomized.Claims.Select(Entry).ToDictionary(static entry => entry.AtomId);
        if (expand)
        {
            foreach (var plan in atomized.ClausePlans)
            {
                var materialized = DigestionDecomposition.Materialize(entries[Id(plan.Parent)], plan, entries);
                entries[materialized.Parent.AtomId] = materialized.Parent;
                foreach (var entry in materialized.NewEntries) entries.Add(entry.AtomId, entry);
            }
        }
        return new AtomContextFixture(bytes, atomized,
            DigestionTestSupport.Document(AtomizerRegistry.GenericId,
                entries.Values.OrderByDescending(static entry => entry.AtomId, StringComparer.Ordinal).ToImmutableArray()));
    }

    internal static string Id(DigestionAtom atom) => atom.Fingerprints.RawSha256[7..];
    internal static DigestionLedgerEntry Entry(DigestionAtom atom) =>
        DigestionTestSupport.Entry(atom, Id(atom), AtomizerRegistry.GenericId);
    internal AtomContextFixture WithEntries(IEnumerable<DigestionLedgerEntry> entries) => this with
    {
        Ledger = Ledger.WithDigestionSources([Ledger.RequireDigestionSources().Single() with
        {
            Entries = entries.ToImmutableArray(),
        }]),
    };

    internal RawRepositorySnapshot RawSnapshot(bool includeSource = true)
    {
        var files = new List<RawRepositoryEntry>
        {
            new(TheoryAtomizerDataLoader.DataPath, [.. DigestionTestSupport.RulesBytes]),
        };
        if (includeSource) files.Add(new RawRepositoryEntry(SourcePath, [.. SourceBytes]));
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
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(RawSnapshot(includeSource))).Snapshot;

    internal ProductionCliEnvironment Environment(string root = "/repo") => new(root,
        new FakeRepositoryGateway(RawChangeSet.Create([]), RawSnapshot(), null), new FakeLeanReportSource(null));
}
