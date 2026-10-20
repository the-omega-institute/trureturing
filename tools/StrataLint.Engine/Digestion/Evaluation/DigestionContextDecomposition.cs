using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static class DigestionContextDecomposition
{
    internal static RawRepositorySnapshot Expand(RawRepositorySnapshot raw, BackfillInventoryDocument ledger,
        DigestionLedgerEntry parent, ImmutableArray<DigestionContextPointerIndex> versions,
        out ImmutableArray<DigestionCasObject> contextCas)
    {
        var parentBody = raw.Entries.Single(file => file.Path == DigestionCasStore.RootPath + parent.AtomId).Bytes;
        // The local writer parses the immutable parent CAS only. Its offsets are
        // translated into each saved occurrence; current source text is irrelevant.
        var localRaw = RawRepositorySnapshot.Create(raw.Entries.Where(file => file.Path != parent.SourcePath)
            .Append(new RawRepositoryEntry(parent.SourcePath, parentBody)));
        var snapshot = Decode(localRaw);
        var local = DigestionContextIndexBuilder.Build(snapshot, ledger, parent.SourceId);
        contextCas = local.CasObjects;
        var result = raw;
        var leaves = local.Index.Entries.SelectMany(entry => entry.Occurrences
                .Select(item => (entry.AtomId, Occurrence: item)))
            .Where(item => item.AtomId != parent.AtomId && !ledger.RequireDigestionEntries()
                .Any(entry => entry.AtomId == item.AtomId && !entry.Receipts.ChainAtoms.IsEmpty)).ToArray();
        if (leaves.Length == 0) throw new FormatException("context decomposition has no leaves");
        foreach (var version in versions)
        {
            var parentOccurrences = version.Entries[0].Occurrences;
            var savedEntries = result.Entries.Where(file => file.Path.StartsWith(
                    BackfillInventoryLoader.RootPath + version.SourceId + "/context/", StringComparison.Ordinal))
                .Select(file => DigestionContextPointerStore.ParseVersions(file.Bytes, version.SourceId,
                    Path.GetFileNameWithoutExtension(file.Path)).SingleOrDefault(item => item.SourceSha256 == version.SourceSha256))
                .OfType<DigestionContextPointerIndex>().Select(item => item.Entries[0]).ToArray();
            var oldCount = savedEntries.SelectMany(entry => entry.Occurrences).Max(item => item.StreamCount);
            var deltas = parentOccurrences.Select(item => (Occurrence: item,
                Delta: leaves.Length - (oldCount - item.StreamCount + 1))).ToArray();
            // Ranks are display metadata. Account for the old subtree as well as
            // the new one, including a reconciliation that retains the same leaves.
            var adjustedEntries = ImmutableArray.CreateBuilder<DigestionContextPointerEntry>();
            foreach (var savedEntry in savedEntries)
            {
                var id = savedEntry.AtomId;
                var adjusted = savedEntry.Occurrences.Select(item => item with
                {
                    StreamIndex = item.StreamIndex + deltas.Where(change => change.Occurrence.EndByte <= item.StartByte).Sum(change => change.Delta),
                    StreamCount = item.StreamCount + deltas.Where(change =>
                        change.Occurrence.EndByte <= item.StartByte || change.Occurrence.StartByte >= item.EndByte).Sum(change => change.Delta),
                }).ToImmutableArray();
                adjustedEntries.Add(new DigestionContextPointerEntry(id, adjusted));
            }
            result = DigestionContextPointerStore.Add(result, version with { Entries = adjustedEntries.ToImmutable() });
            var changes = new Dictionary<string, List<DigestionContextOccurrence>>(StringComparer.Ordinal);
            foreach (var occurrence in version.Entries[0].Occurrences)
            {
                foreach (var entry in local.Index.Entries.Where(entry => entry.AtomId != parent.AtomId))
                    foreach (var child in entry.Occurrences)
                    {
                        var composed = child with
                        {
                            StartByte = occurrence.StartByte + child.StartByte,
                            EndByte = occurrence.StartByte + child.EndByte,
                            StreamIndex = occurrence.StreamIndex - 1 + child.StreamIndex
                                + deltas.Where(change => change.Occurrence.EndByte <= occurrence.StartByte).Sum(change => change.Delta),
                            StreamCount = occurrence.StreamCount - 1 + child.StreamCount + deltas.Where(change => change.Occurrence.StartByte != occurrence.StartByte).Sum(change => change.Delta),
                            PreviousAtomId = child.PreviousAtomId ?? occurrence.PreviousAtomId,
                            NextAtomId = child.NextAtomId ?? occurrence.NextAtomId,
                            PreviousStartByte = child.PreviousStartByte is { } before
                                ? occurrence.StartByte + before : occurrence.PreviousStartByte,
                            NextStartByte = child.NextStartByte is { } after
                                ? occurrence.StartByte + after : occurrence.NextStartByte,
                            GoverningContext = MergeScopes(occurrence.GoverningContext, child.GoverningContext, raw, local.CasObjects),
                        };
                        Add(entry.AtomId, composed);
                    }
                var first = leaves.MinBy(item => item.Occurrence.StartByte);
                var last = leaves.MaxBy(item => item.Occurrence.EndByte);
                ReplaceExterior(occurrence.PreviousAtomId, occurrence.PreviousStartByte,
                    first.AtomId, occurrence.StartByte + first.Occurrence.StartByte, next: true);
                ReplaceExterior(occurrence.NextAtomId, occurrence.NextStartByte,
                    last.AtomId, occurrence.StartByte + last.Occurrence.StartByte, next: false);
            }
            foreach (var (id, occurrences) in changes)
            {
                var old = Existing(id);
                var merged = old.Where(item => !occurrences.Any(change => change.StartByte == item.StartByte))
                    .Concat(occurrences).OrderBy(item => item.StartByte)
                    .Select((item, index) => item with { OccurrenceIndex = index + 1 }).ToImmutableArray();
                result = DigestionContextPointerStore.Add(result, version with
                {
                    Entries = [new DigestionContextPointerEntry(id, merged)],
                });
            }

            void Add(string id, DigestionContextOccurrence occurrence)
            {
                if (!changes.TryGetValue(id, out var list)) changes[id] = list = [];
                var prior = list.FindIndex(item => item.StartByte == occurrence.StartByte);
                if (prior >= 0) list[prior] = occurrence;
                else list.Add(occurrence);
            }

            ImmutableArray<DigestionContextOccurrence> Existing(string id)
            {
                var path = DigestionContextPointerIndex.RelativePath(version.SourceId, id);
                var file = result.Entries.SingleOrDefault(file => file.Path == path);
                return file is null ? [] : DigestionContextPointerStore.ParseVersions(file.Bytes, version.SourceId, id)
                    .SingleOrDefault(item => item.SourceSha256 == version.SourceSha256)?.Entries[0].Occurrences ?? [];
            }

            void ReplaceExterior(string? id, int? start, string replacement, int replacementStart, bool next)
            {
                if (id is null) return;
                var exterior = Existing(id).SingleOrDefault(item => item.StartByte == start)
                    ?? throw new FormatException($"CONTEXT_REFERENCE_MISSING atom_id={id}");
                Add(id, next ? exterior with { NextAtomId = replacement, NextStartByte = replacementStart }
                    : exterior with { PreviousAtomId = replacement, PreviousStartByte = replacementStart });
            }
        }
        return result;
    }

    private static ImmutableArray<DigestionContextScopePointer> MergeScopes(
        ImmutableArray<DigestionContextScopePointer> inherited, ImmutableArray<DigestionContextScopePointer> local,
        RawRepositorySnapshot raw, ImmutableArray<DigestionCasObject> captured)
    {
        var levels = local.Where(scope => scope.Relation == "heading").Select(Level).ToArray();
        var minimum = levels.Length == 0 ? int.MaxValue : levels.Min();
        var headings = inherited.Where(scope => scope.Relation == "heading" && Level(scope) < minimum)
            .Concat(local.Where(scope => scope.Relation == "heading"));
        var scopes = inherited.Where(scope => scope.Relation != "heading")
            .Concat(local.Where(scope => scope.Relation != "heading"
                && !inherited.Any(outer => outer.Relation == scope.Relation)));
        return headings.Concat(scopes.OrderBy(scope => scope.Relation == "enclosing-scope" ? 1 : 0))
            .Distinct().ToImmutableArray();

        int Level(DigestionContextScopePointer scope)
        {
            var path = DigestionCasStore.RootPath + scope.AtomId;
            var bytes = captured.FirstOrDefault(item => item.RelativePath == path)?.Bytes
                ?? raw.Entries.Single(item => item.Path == path).Bytes;
            return MarkdigBlockAst.ParseOwned(Encoding.UTF8.GetString(bytes.AsSpan()))
                .OfType<MarkdownHeading>().Single().Level;
        }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new FormatException(failure.Message),
    };
}
