using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class AtomContextMigrationCommand
{
    // An existing observation can be reused without rebuilding distant roots.
    // Check the selected subtrees against their actual enclosing/neighbor chains;
    // retain the saved ranks and graph only when those local edges still agree.
    private static (RawRepositorySnapshot Raw, RepositorySnapshot Snapshot, BackfillInventoryDocument Document,
        DigestionContextPointerIndex? SavedIndex)? TryUseSavedGraph(IRepositoryGateway repository,
        RawRepositorySnapshot raw, DigestionLedgerSource source, IReadOnlyList<string> atomIds,
        ImmutableArray<byte> observed, RawRepositorySnapshot bodies)
    {
        var hash = DigestionFingerprint.ComputeOpaque(observed.AsSpan()).RawSha256;
        var rows = raw.Entries.Where(file => DigestionContextPointerStore.IsCanonicalPath(file.Path))
            .SelectMany(file => DigestionContextPointerStore.ParseVersions(file.Bytes, source.SourceId,
                Path.GetFileNameWithoutExtension(file.Path)))
            .Where(index => index.SourceSha256 == hash).ToArray();
        foreach (var row in rows)
            if (row.SourcePath != source.SourcePath || row.Atomizer != source.Atomizer)
                throw new FormatException($"CONTEXT_VERSION_CONFLICT source_id={source.SourceId}");
        if (rows.Length == 0) return null;
        var spans = bodies.Entries.SelectMany(body => DigestionAtomContextProjection.OccurrenceStarts(observed, body.Bytes)
            .Select(start => (Id: Path.GetFileName(body.Path), Start: start, End: start + body.Bytes.Length))).ToArray();
        var roots = spans.Where(span => !spans.Any(other => other.Start <= span.Start && other.End >= span.End
            && other.End - other.Start > span.End - span.Start)).ToArray();
        roots = roots.Where(span => !roots.Any(other => span.Start != other.Start
            && span.Start < other.End && other.Start < span.End)).ToArray();
        foreach (var graph in rows.GroupBy(row => row.VersionKey, StringComparer.Ordinal))
        {
            var entries = graph.ToDictionary(row => row.Entries[0].AtomId, row => row.Entries[0], StringComparer.Ordinal);
            if (atomIds.Any(id => !entries.ContainsKey(id))) continue;
            var selected = atomIds.SelectMany(id => entries[id].Occurrences).ToArray();
            var neighbors = selected.SelectMany(item => new[] { (item.PreviousAtomId, item.PreviousStartByte),
                (item.NextAtomId, item.NextStartByte) }).Where(item => item.Item1 is not null).ToArray();
            var intervals = selected.Concat(neighbors.Select(item => entries[item.Item1!].Occurrences
                .Single(occurrence => occurrence.StartByte == item.Item2))).ToArray();
            var relevantIds = roots.Where(root => intervals.Any(item => root.Start < item.EndByte && item.StartByte < root.End))
                .Select(root => root.Id).Concat(neighbors.Select(item => item.Item1!)).Concat(atomIds)
                .Distinct(StringComparer.Ordinal).ToArray();
            var accounts = DigestionQuerySelection.ReadAtoms(repository, relevantIds);
            var scoped = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(raw, accounts.Raw));
            scoped = DigestionQuerySelection.Load(DigestionQuerySelection.Merge(scoped.Raw, repository.ReadCurrent(
                scoped.Document.RequireDigestionEntries().Select(DigestionQuerySelection.CasPath).ToArray())));
            scoped = DigestionQuerySelection.ReadChains(repository, scoped);
            var built = DigestionContextIndexBuilder.Build(scoped.Snapshot, scoped.Document, source.SourceId).Index;
            var actual = built.Entries.ToDictionary(entry => entry.AtomId, StringComparer.Ordinal);
            var byId = scoped.Document.RequireDigestionEntries().ToDictionary(entry => entry.AtomId, StringComparer.Ordinal);
            var pending = new Stack<string>(atomIds);
            var closure = new HashSet<string>(StringComparer.Ordinal);
            while (pending.TryPop(out var id))
                if (closure.Add(id)) foreach (var child in byId[id].Receipts.ChainAtoms) pending.Push(child);
            if (closure.Any(id => !entries.TryGetValue(id, out var saved) || !actual.TryGetValue(id, out var current)
                || !saved.Occurrences.Select(Edge).SequenceEqual(current.Occurrences.Select(Edge))
                || !saved.Occurrences.SelectMany(item => item.GoverningContext)
                    .SequenceEqual(current.Occurrences.SelectMany(item => item.GoverningContext)))) continue;
            var index = graph.First() with { Entries = [.. entries.Values.OrderBy(entry => entry.AtomId, StringComparer.Ordinal)] };
            return (scoped.Raw, scoped.Snapshot, scoped.Document, index);
        }
        return null;

        static object Edge(DigestionContextOccurrence item) => (item.StartByte, item.EndByte,
            item.PreviousAtomId, item.PreviousStartByte, item.NextAtomId, item.NextStartByte);
    }
}
