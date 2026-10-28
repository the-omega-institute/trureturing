using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed class DecomposeFixture
{
    internal const string Dialect = AtomizerRegistry.GenericId;
    internal const string Bold = "**Theorem 1.1** First assertion.\n\n**Second** Second assertion.\n";
    internal static string Eight => "**Theorem 1.1** First obligation α.\n\n"
        + string.Concat(Enumerable.Range(2, 7)
            .Select(index => $"**Clause {index}** Independent obligation {index} α.\n\n"));
    internal DecomposeFixture(string text = Bold, string atomizer = Dialect)
    {
        Parent = Entry(text, atomizer);
        var source = new DigestionLedgerSource("probe", "docs/probe.md", atomizer, [],
            GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry), [Parent]);
        Current = DigestionTestSupport.WithSourcePolicy(RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText("docs/probe.md", text),
            new RawRepositoryEntry("Meta/Digestion/backfill/probe/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)),
            new RawRepositoryEntry(PathFor(Parent), BackfillInventoryWriter.WriteAtom(Parent)),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + Parent.AtomId, text),
        ]), ["docs/*.md"]);
        if (AtomizerRegistry.IsRegistered(atomizer)) CaptureContext();
        Baseline = Current;
        Gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Current, Baseline,
            currentReader: () => Current);
    }

    internal DigestionLedgerEntry Parent { get; }
    internal RawRepositorySnapshot Current { get; set; }

    internal void CaptureContext(params string[] sourceIds)
    {
        var decoded = Decode(Current);
        var ledger = BackfillInventoryLoader.LoadForDigestion(decoded);
        foreach (var source in ledger.RequireDigestionSources().Where(source => sourceIds.Length == 0 || sourceIds.Contains(source.SourceId)))
        {
            var built = DigestionContextIndexBuilder.Build(decoded, ledger, source.SourceId);
            var files = Current.Entries.Where(file => !file.Path.StartsWith(
                BackfillInventoryLoader.RootPath + source.SourceId + "/context/", StringComparison.Ordinal))
                .ToDictionary(file => file.Path, StringComparer.Ordinal);
            foreach (var item in built.CasObjects) files[item.RelativePath] = new RawRepositoryEntry(item.RelativePath, item.Bytes);
            Current = DigestionContextPointerStore.Add(RawRepositorySnapshot.Create(files.Values), built.Index);
        }
    }

    internal RawRepositorySnapshot Baseline { get; }
    internal FakeRepositoryGateway Gateway { get; }
    internal int Writes { get; private set; }
    internal ImmutableArray<DigestionCasObject> CasWrites { get; private set; } = [];
    internal ImmutableArray<IngestCommand.LedgerUpdate> LedgerWrites { get; private set; } = [];
    internal RepositorySnapshot Snapshot => Decode(Current);
    internal BackfillInventoryDocument Document => BackfillInventoryLoader.Load(Snapshot);
    internal string[] Args(string? atomId = null, bool dryRun = false) =>
        ["--atom", atomId ?? Parent.AtomId, .. dryRun ? new[] { "--dry-run" } : []];

    internal void Apply(string _, RawRepositorySnapshot expected,
        ImmutableArray<DigestionCasObject> cas, ImmutableArray<IngestCommand.LedgerUpdate> updates)
    {
        var currentByPath = Current.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        foreach (var entry in expected.Entries)
        {
            Assert.True(currentByPath.TryGetValue(entry.Path, out var current),
                $"scoped writer input omitted {entry.Path}");
            Assert.Equal(entry.Bytes.ToArray(), current.Bytes.ToArray());
        }
        Writes++;
        CasWrites = cas;
        LedgerWrites = updates;
        var entries = Current.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        foreach (var item in cas)
            entries[item.RelativePath] = new RawRepositoryEntry(item.RelativePath, item.Bytes);
        foreach (var item in updates)
        {
            if (item.Bytes is { } bytes) entries[item.Path] = new RawRepositoryEntry(item.Path, bytes);
            else entries.Remove(item.Path);
        }
        Current = RawRepositorySnapshot.Create(entries.Values);
    }

    internal void Replace(DigestionLedgerEntry entry)
    {
        Current = RawRepositorySnapshot.Create(Current.Entries
            .Where(item => !item.Path.EndsWith("/" + entry.AtomId + ".yaml", StringComparison.Ordinal))
            .Append(new RawRepositoryEntry(PathFor(entry), BackfillInventoryWriter.WriteAtom(entry))));
    }

    internal void Add(DigestionLedgerEntry entry, string text)
    {
        Current = RawRepositorySnapshot.Create(Current.Entries.Where(file => file.Path != DigestionCasStore.RootPath + entry.AtomId).Concat(new RawRepositoryEntry[]
        {
            new RawRepositoryEntry(PathFor(entry), BackfillInventoryWriter.WriteAtom(entry)),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + entry.AtomId, text),
        }));
    }

    internal static DigestionLedgerEntry Entry(string text, string atomizer = Dialect)
    {
        var bytes = Encoding.UTF8.GetBytes(text);
        var fingerprint = DigestionFingerprint.Compute(bytes);
        return new DigestionLedgerEntry("probe", "docs/probe.md", atomizer,
            fingerprint.RawSha256[7..], fingerprint, [], new DigestionReceipts([], [], null),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            fingerprint.RawSha256);
    }

    internal static string PathFor(DigestionLedgerEntry entry) =>
        $"Meta/Digestion/backfill/{entry.SourceId}/"
        + $"{DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)}/{entry.AtomId}.yaml";

    internal static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(DigestionTestSupport.WithSourcePolicy(raw))).Snapshot;

    internal static DigestionAtom Atom(string text) =>
        DigestionAtom.FromFrozenCas([.. Encoding.UTF8.GetBytes(text)]);
}
