using System.Collections.Immutable;

namespace StrataLint.Engine;

/// <summary>
/// The durable adjacency index for a source.  Atom bodies remain content addressed
/// in the normal CAS; this file stores only the source-version binding and pointers
/// needed to walk the already captured atom bodies.
/// </summary>
internal sealed record DigestionContextPointerIndex(
    string SourceId,
    string SourcePath,
    string Atomizer,
    string SourceSha256,
    ImmutableArray<DigestionContextPointerEntry> Entries)
{
    internal const int SchemaVersion = 1;
    internal static string RelativePath(string sourceId, string atomId) =>
        BackfillInventoryLoader.RootPath + sourceId + "/context/" + atomId + ".json";
}

internal sealed record DigestionContextPointerEntry(
    string AtomId,
    ImmutableArray<DigestionContextOccurrence> Occurrences);

internal sealed record DigestionContextOccurrence(
    int OccurrenceIndex,
    int StreamIndex,
    int StreamCount,
    string? PreviousAtomId,
    string? NextAtomId,
    int StartByte,
    int EndByte,
    int? PreviousStartByte,
    int? NextStartByte,
    ImmutableArray<DigestionContextScopePointer> GoverningContext);

internal sealed record DigestionContextScopePointer(string Relation, string AtomId);

internal sealed record DigestionContextIndexBuild(
    DigestionContextPointerIndex Index,
    ImmutableArray<DigestionCasObject> CasObjects);

internal static class DigestionContextIndexBuilder
{
    internal static DigestionContextIndexBuild Build(
        RepositorySnapshot snapshot,
        BackfillInventoryDocument ledger,
        string sourceId,
        AtomizedTheoryDocument? atomized = null)
    {
        var source = ledger.RequireDigestionSources().SingleOrDefault(item => item.SourceId == sourceId)
            ?? throw new FormatException($"context source is absent: {sourceId}");
        if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
            throw new FormatException($"context source is missing: {source.SourcePath}");
        var stream = DigestionAtomContextProjection.MaterializeSource(snapshot, ledger, sourceId, atomized);
        var cas = new Dictionary<string, DigestionCasObject>(StringComparer.Ordinal);
        var grouped = new Dictionary<string, List<DigestionContextOccurrence>>(StringComparer.Ordinal);
        foreach (var atom in stream.Atoms)
            Capture(atom.RawBytes, cas);
        var contexts = stream.PersistedContexts().ToList();
        var capturedIds = contexts.Select(item => item.AtomId).ToHashSet(StringComparer.Ordinal);
        foreach (var entry in source.Entries.Where(entry => !capturedIds.Contains(entry.AtomId)))
        {
            if (!snapshot.TryGetFile(DigestionCasStore.RootPath + entry.AtomId, out var body)) continue;
            var atom = DigestionAtom.FromFrozenCas(body.RawBytes);
            if (entry.AtomId != atom.Fingerprints.RawSha256[7..] || entry.CasRef != atom.Fingerprints.RawSha256
                || entry.Fingerprints != atom.Fingerprints) throw new FormatException($"CAS_MISMATCH atom_id={entry.AtomId}");
            foreach (var start in DigestionAtomContextProjection.OccurrenceStarts(sourceFile.RawBytes, body.RawBytes))
            {
                var end = start + body.RawBytes.Length;
                // A registered regrouping can lie outside the active chain while
                // covering complete leaves. Crossing an existing leaf would require
                // a different cut and remains unresolved rather than inventing one.
                if (stream.Atoms.Any(leaf => leaf.StartByte < start && start < leaf.EndByte
                    || leaf.StartByte < end && end < leaf.EndByte)) continue;
                contexts.Add((entry.AtomId, stream.ContextForStoredSpan(entry,
                    atom with { StartByte = start, EndByte = end })));
            }
        }
        foreach (var (atomId, context) in contexts)
        {
            var occurrence = new DigestionContextOccurrence(
                0,
                context.Index,
                context.Count,
                context.Previous?.AtomId,
                context.Next?.AtomId,
                context.StartByte,
                context.EndByte,
                context.PreviousStartByte,
                context.NextStartByte,
                context.GoverningContext.Select(item =>
                {
                    var captured = Capture(item.RawBytes, cas);
                    return new DigestionContextScopePointer(item.Relation, captured.Reference[7..]);
                }).ToImmutableArray());
            if (!grouped.TryGetValue(atomId, out var prior)) grouped[atomId] = prior = [];
            if (!prior.Any(existing => existing.StreamIndex == occurrence.StreamIndex
                && existing.PreviousAtomId == occurrence.PreviousAtomId
                && existing.NextAtomId == occurrence.NextAtomId))
                prior.Add(occurrence);
        }

        var sourceHash = DigestionFingerprint.ComputeOpaque(sourceFile.RawBytes.AsSpan()).RawSha256;
        var entries = grouped.OrderBy(static pair => pair.Key, StringComparer.Ordinal)
            .Select(static pair => new DigestionContextPointerEntry(pair.Key,
                pair.Value.OrderBy(static occurrence => occurrence.StreamIndex)
                    .Select((occurrence, index) => occurrence with { OccurrenceIndex = index + 1 })
                    .ToImmutableArray()))
            .ToImmutableArray();
        return new DigestionContextIndexBuild(
            new DigestionContextPointerIndex(source.SourceId, source.SourcePath, source.Atomizer, sourceHash, entries),
            cas.Values.OrderBy(static item => item.RelativePath, StringComparer.Ordinal).ToImmutableArray());
    }

    private static DigestionCasObject Capture(
        ImmutableArray<byte> bytes,
        IDictionary<string, DigestionCasObject> cas)
    {
        var captured = DigestionCasStore.Capture(bytes.AsSpan());
        if (cas.TryGetValue(captured.Reference, out var existing)) return existing;
        cas.Add(captured.Reference, captured);
        return captured;
    }
}
