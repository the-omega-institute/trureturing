using System.Collections.Immutable;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal sealed class DecomposeFixture
{
    internal const string Dialect = "dialect:decompose-probe";
    internal const string Bold = "**Theorem 1.1** First assertion.\n\n**Second** Second assertion.\n";
    internal const string Eight = "**Theorem 1.1**\n\nThe obligations follow.\n\n"
        + "- obligation one\n- obligation two\n- obligation three\n- obligation four\n"
        + "- obligation five\n- obligation six\n- obligation seven\n- obligation eight\n\nClosing remark.\n";
    internal static string RulesText => TheoryAtomizerDataTests.Minimal + "\n\n" + """
        [[dialect]]
        id = "decompose-probe"
        claim = "^\\*\\*(?<kind>Theorem)\\s+(?<number>[0-9]+\\.[0-9]+)"

        [[dialect.genre]]
        dialect = "decompose-probe"
        token = "Theorem"
        kind = "theorem"
        """ + "\n";

    internal DecomposeFixture(string text = Bold, string atomizer = Dialect)
    {
        Parent = Entry(text, atomizer);
        var source = new DigestionLedgerSource("probe", "docs/probe.md", atomizer, [],
            GenreRegistryProjection.Available(GenreRegistryCheck.Collected([])), [Parent]);
        Current = RawRepositorySnapshot.Create(
        [
            RawRepositoryEntry.FromText(TheoryAtomizerDataLoader.DataPath, RulesText),
            RawRepositoryEntry.FromText("docs/probe.md", text),
            new RawRepositoryEntry("Meta/Digestion/backfill/probe/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source)),
            new RawRepositoryEntry(PathFor(Parent), BackfillInventoryWriter.WriteAtom(Parent)),
            RawRepositoryEntry.FromText(DigestionCasStore.RootPath + Parent.AtomId, text),
        ]);
        Baseline = Current;
        Gateway = new FakeRepositoryGateway(RawChangeSet.Create([]), Current, Baseline,
            currentReader: () => Current);
    }

    internal DigestionLedgerEntry Parent { get; }
    internal RawRepositorySnapshot Current { get; set; }
    internal RawRepositorySnapshot Baseline { get; }
    internal FakeRepositoryGateway Gateway { get; }
    internal int Writes { get; private set; }
    internal ImmutableArray<DigestionCasObject> CasWrites { get; private set; } = [];
    internal ImmutableArray<IngestCommand.LedgerUpdate> LedgerWrites { get; private set; } = [];
    internal RepositorySnapshot Snapshot => Decode(Current);
    internal BackfillInventoryDocument Document => BackfillInventoryLoader.Load(Snapshot);
    internal TheoryAtomizerRules Rules => TheoryAtomizerDataLoader.Load(Snapshot);
    internal string[] Args(string? atomId = null, bool dryRun = false) =>
        ["--atom", atomId ?? Parent.AtomId, "--base", "baseline", .. dryRun ? new[] { "--dry-run" } : []];

    internal void Apply(string _, RawRepositorySnapshot expected,
        ImmutableArray<DigestionCasObject> cas, ImmutableArray<IngestCommand.LedgerUpdate> updates)
    {
        Assert.Same(Current, expected);
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
        Current = RawRepositorySnapshot.Create(Current.Entries.Concat(new RawRepositoryEntry[]
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
            fingerprint.RawSha256[7..], fingerprint, [], new DigestionReceipts([], [], [], null),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open),
            fingerprint.RawSha256);
    }

    internal static string PathFor(DigestionLedgerEntry entry) =>
        $"Meta/Digestion/backfill/{entry.SourceId}/"
        + $"{DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)}/{entry.AtomId}.yaml";

    internal static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(SnapshotDecoder.Decode(raw)).Snapshot;

    internal static DigestionAtom Atom(string text) =>
        DigestionAtom.FromFrozenCas([.. Encoding.UTF8.GetBytes(text)]);
}
