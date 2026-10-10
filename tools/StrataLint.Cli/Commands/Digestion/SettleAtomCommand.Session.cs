using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class SettleAtomCommand
{
    private sealed class Session(IRepositoryGateway repository) : IRepositoryGateway
    {
        private readonly Dictionary<string, (ImmutableArray<byte>? Before, ImmutableArray<byte>? After)> committed =
            new(StringComparer.Ordinal);
        private (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document) loaded =
            DigestionQuerySelection.Load(RawRepositorySnapshot.Create([]));

        internal RawRepositorySnapshot CurrentRaw => loaded.Raw;
        internal RepositorySnapshot Current => loaded.Snapshot;
        internal BackfillInventoryDocument Document => loaded.Document;

        internal void ReadAtom(string atomId) => Merge(DigestionQuerySelection.ReadAtom(this, atomId).Raw);

        internal void ReadContext(string atomId)
        {
            Merge(DigestionQuerySelection.ReadContext(this, atomId, allowMissing: true).Raw);
            var target = LocateTarget(Document, atomId);
            if (!target.Receipts.ChainAtoms.IsEmpty)
                loaded = DigestionQuerySelection.ReadChains(this, loaded, [atomId], allowMissing: true);
        }

        internal void ReadChainEvaluation(DigestionLedgerEntry target)
        {
            var closure = ChainClosureIds(Document, target.AtomId);
            // A reused child's nonpropositional receipt names neighbors in its
            // owning theory. Load that context, even when it belongs to another source.
            var receiptIds = Document.RequireDigestionEntries()
                .Where(entry => closure.Contains(entry.AtomId) && entry.Receipts.Nonpropositional is not null)
                .Select(static entry => entry.AtomId).ToArray();
            foreach (var id in receiptIds) ReadContext(id);
            var entries = Document.RequireDigestionEntries().Where(entry => closure.Contains(entry.AtomId)).ToArray();
            var paths = entries.SelectMany(static entry => entry.CoverageGids
                    .Select(static gid => Gid.TryParse(gid, out var parsed) ? parsed.Path.Value : null)
                    .Append(entry.Receipts.TailAuthorization?.Path)
                    .Append(entry.SourcePath))
                .OfType<string>()
                .Concat(entries.Any(static entry => !entry.Coverage.IsEmpty)
                    ? ["D5", "Reg", "Trureturing.lean", "Golden/Frozen/state"] : Array.Empty<string>())
                .Distinct(StringComparer.Ordinal).ToArray();
            loaded = DigestionWorkingTree.Extend(this, loaded, Decode, paths);
        }

        internal void Commit(ImmutableArray<IngestCommand.LedgerUpdate> updates)
        {
            var entries = CurrentRaw.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
            foreach (var update in updates)
            {
                var before = entries.TryGetValue(update.Path, out var entry) ? (ImmutableArray<byte>?)entry.Bytes : null;
                committed[update.Path] = committed.TryGetValue(update.Path, out var original)
                    ? (original.Before, update.Bytes) : (before, update.Bytes);
                if (update.Bytes is { } bytes) entries[update.Path] = new RawRepositoryEntry(update.Path, bytes);
                else entries.Remove(update.Path);
            }
            loaded = DigestionQuerySelection.Load(RawRepositorySnapshot.Create(entries.Values));
        }

        private void Merge(RawRepositorySnapshot extra) =>
            loaded = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(CurrentRaw, extra));

        public RawRepositorySnapshot ReadCurrent(IReadOnlyList<string> paths)
        {
            var entries = repository.ReadCurrent(paths).Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
            foreach (var (path, change) in committed.Where(item => paths.Any(selection =>
                         GitRepositoryGateway.MatchesPathSelection(item.Key, selection))))
            {
                if (entries.TryGetValue(path, out var entry)
                    && !Equal(entry.Bytes, change.Before) && !Equal(entry.Bytes, change.After))
                    throw new FormatException($"input changed during digestion query: {path}");
                if (change.After is { } bytes) entries[path] = new RawRepositoryEntry(path, bytes);
                else entries.Remove(path);
            }
            return RawRepositorySnapshot.Create(entries.Values);
        }

        public IReadOnlyList<string> SearchCurrentPaths(IReadOnlyList<string> paths)
        {
            var results = repository.SearchCurrentPaths(paths).ToHashSet(StringComparer.Ordinal);
            foreach (var (path, change) in committed.Where(item => paths.Any(selection =>
                         GitRepositoryGateway.MatchesPathSelection(item.Key, selection))))
            {
                if (change.After is null) results.Remove(path);
                else results.Add(path);
            }
            return results.Order(StringComparer.Ordinal).ToArray();
        }

        private static bool Equal(ImmutableArray<byte> actual, ImmutableArray<byte>? expected) =>
            expected is { } bytes && actual.AsSpan().SequenceEqual(bytes.AsSpan());

        public AdmissionTopologyOutcome InspectAdmissionTopology() => repository.InspectAdmissionTopology();
        public PreparedRepository Prepare(string? protectedBase) => repository.Prepare(protectedBase);
        public FrozenRevisionIdentity ResolveCurrentRevision() => repository.ResolveCurrentRevision();
        public RawRepositorySnapshot ReadCurrent() => throw new InvalidOperationException("settlement requires an explicit read scope");
        public RawRepositorySnapshot ReadRevision(string revision) => repository.ReadRevision(revision);
        public RawChangeSet ReadCurrentChanges() => repository.ReadCurrentChanges();
        public RawChangeSet ReadChanges(string revision) => repository.ReadChanges(revision);
    }
}
