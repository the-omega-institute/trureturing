using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal enum DigestionAtomContextError
{
    ARGUMENTS_INVALID,
    ATOM_ABSENT,
    ATOM_AMBIGUOUS,
    SOURCE_MISSING,
    ATOMIZER_UNSUPPORTED,
    OCCURRENCE_MISSING,
    OCCURRENCE_AMBIGUOUS,
}

internal sealed class DigestionAtomContextException(DigestionAtomContextError code, string detail)
    : Exception(detail)
{
    internal DigestionAtomContextError Code { get; } = code;
}

internal sealed record DigestionAtomContext(
    DigestionLedgerEntry Target,
    (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? Previous,
    (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes) Current,
    (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? Next,
    int Index,
    int Count,
    string SourceId,
    string SourcePath,
    string Atomizer)
{
    internal string? SourceSha256 { get; init; }
    internal string? GraphSha256 { get; init; }
    internal int StartByte { get; init; }
    internal int EndByte { get; init; }
    internal int? PreviousStartByte { get; init; }
    internal int? NextStartByte { get; init; }
    internal ImmutableArray<DigestionGoverningContext> GoverningContext { get; init; } = [];
    internal string? PreviousBoundaryReason => Previous is null ? "source-start" : null;
    internal string? NextBoundaryReason => Next is null ? "source-end" : null;
}

internal sealed record DigestionGoverningContext(string Relation, ImmutableArray<byte> RawBytes);

internal static class DigestionAtomContextProjection
{
    internal static DigestionAtomContext Resolve(
        RepositorySnapshot snapshot, BackfillInventoryDocument ledger, string atomId)
    {
        var occurrences = ResolveOccurrences(snapshot, ledger, atomId);
        if (occurrences.Length != 1)
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_AMBIGUOUS,
                $"atom_id={atomId} occurrences={occurrences.Length}");
        return occurrences[0];
    }

    internal static ImmutableArray<DigestionAtomContext> ResolveOccurrences(
        RepositorySnapshot snapshot, BackfillInventoryDocument ledger, string atomId, AtomizedTheoryDocument? sourceDocument = null)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(ledger);
        ValidateAtomId(atomId);
        var target = RequireTarget(ledger.RequireDigestionEntries(), atomId);
        try
        {
            ValidateContextChain(snapshot, ledger, target);
            return DigestionContextPointerStore.Load(snapshot, target.SourceId, atomId)
                .SelectMany(pointers => ResolvePersistedOccurrences(snapshot, ledger, target, pointers))
                .ToImmutableArray();
        }
        catch (Exception error) when (error is FormatException or InvalidOperationException or ArgumentException)
        {
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING, error.Message);
        }
    }

    private static ImmutableArray<DigestionAtomContext> ResolvePersistedOccurrences(
        RepositorySnapshot snapshot,
        BackfillInventoryDocument ledger,
        DigestionLedgerEntry target,
        DigestionContextPointerIndex pointers)
    {
        var pointer = pointers.Entries.SingleOrDefault(entry => entry.AtomId == target.AtomId);
        if (pointer is null)
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING,
                $"atom_id={target.AtomId} source_id={target.SourceId}");

        var byId = ledger.RequireDigestionEntries()
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Select(group => group.SingleOrDefault(entry => entry.SourceId == target.SourceId)
                ?? (group.Count() == 1 ? group.Single()
                    : throw new FormatException($"context neighbor atom_id={group.Key} count={group.Count()}")))
            .ToDictionary(static entry => entry.AtomId, StringComparer.Ordinal);
        var contexts = ImmutableArray.CreateBuilder<DigestionAtomContext>(pointer.Occurrences.Length);
        foreach (var occurrence in pointer.Occurrences)
        {
            _ = DigestionContextPointerStore.Follow(snapshot, pointers, occurrence, next: false);
            _ = DigestionContextPointerStore.Follow(snapshot, pointers, occurrence, next: true);
            var current = ReadPointerBody(snapshot, target.AtomId);
            var previous = ReadPointerNeighbor(snapshot, byId, occurrence.PreviousAtomId);
            var next = ReadPointerNeighbor(snapshot, byId, occurrence.NextAtomId);
            var governing = occurrence.GoverningContext.Select(scope =>
                new DigestionGoverningContext(scope.Relation, ReadPointerBody(snapshot, scope.AtomId)))
                .ToImmutableArray();
            contexts.Add(new DigestionAtomContext(
                target,
                previous,
                (target.AtomId, State(byId.GetValueOrDefault(target.AtomId)), current),
                next,
                occurrence.StreamIndex,
                occurrence.StreamCount,
                pointers.SourceId,
                pointers.SourcePath,
                pointers.Atomizer)
            {
                GoverningContext = governing,
                SourceSha256 = pointers.SourceSha256,
                GraphSha256 = pointers.GraphSha256,
                StartByte = occurrence.StartByte, EndByte = occurrence.EndByte,
                PreviousStartByte = occurrence.PreviousStartByte, NextStartByte = occurrence.NextStartByte,
            });
        }
        return contexts.ToImmutable();
    }

    private static ImmutableArray<byte> ReadPointerBody(RepositorySnapshot snapshot, string atomId)
    {
        if (!snapshot.TryGetFile(DigestionCasStore.RootPath + atomId, out var file))
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING,
                $"CAS_MISSING atom_id={atomId}");
        if (DigestionCasStore.Capture(file.RawBytes.AsSpan()).Reference != "sha256:" + atomId)
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING,
                $"CAS_MISMATCH atom_id={atomId}");
        return file.RawBytes;
    }

    private static (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes)? ReadPointerNeighbor(
        RepositorySnapshot snapshot,
        IReadOnlyDictionary<string, DigestionLedgerEntry> byId,
        string? atomId)
    {
        if (atomId is null) return null;
        var bytes = ReadPointerBody(snapshot, atomId);
        return (atomId, byId.TryGetValue(atomId, out var entry) ? State(entry) : null, bytes);
    }

    private static string State(DigestionLedgerEntry? entry) => entry is null
        ? throw new ArgumentNullException(nameof(entry))
        : DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
            + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);

    private static void ValidateContextChain(RepositorySnapshot snapshot, BackfillInventoryDocument ledger, DigestionLedgerEntry target)
    {
        var groups = ledger.RequireDigestionEntries().ToLookup(entry => entry.AtomId, StringComparer.Ordinal);
        var unique = groups.Where(group => group.Count() == 1).ToDictionary(group => group.Key, group => group.Single(), StringComparer.Ordinal);
        var pending = new Stack<string>([target.AtomId]);
        var visited = new HashSet<string>(StringComparer.Ordinal);
        while (pending.TryPop(out var id))
        {
            if (!visited.Add(id)) continue;
            if (!unique.TryGetValue(id, out var entry)) throw new FormatException($"chain atom_id={id} count={groups[id].Count()}");
            var bytes = ReadPointerBody(snapshot, id);
            if (entry.CasRef != "sha256:" + id || entry.Fingerprints != DigestionFingerprint.Compute(bytes.AsSpan()))
                throw new FormatException($"CAS_MISMATCH atom_id={id}");
            if (entry.Receipts.ChainAtoms.IsEmpty) continue;
            var plan = DigestionDecomposition.Plan(entry, bytes, AtomizerRegistry.Require(entry.Atomizer).Atomize, snapshot);
            var materialized = DigestionDecomposition.Materialize(entry, plan, unique);
            if (!materialized.NewEntries.IsEmpty) throw new FormatException($"chain atom is absent for parent {id}");
            foreach (var child in entry.Receipts.ChainAtoms) pending.Push(child);
        }
    }

    private static void ValidateAtomId(string atomId)
    {
        if (string.IsNullOrWhiteSpace(atomId) || !DigestionFingerprint.IsCanonicalSha256("sha256:" + atomId))
            throw new DigestionAtomContextException(DigestionAtomContextError.ARGUMENTS_INVALID,
                "atom_id must be 64 lowercase hexadecimal characters");
    }

    private static DigestionLedgerEntry RequireTarget(IEnumerable<DigestionLedgerEntry> entries, string atomId)
    {
        var targets = entries.Where(entry => entry.AtomId == atomId).ToArray();
        if (targets.Length == 0)
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOM_ABSENT, $"atom_id={atomId}");
        if (targets.Length != 1)
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOM_AMBIGUOUS, $"atom_id={atomId}");
        return targets[0];
    }

    /// <summary>Materializes a source once; callers retain the immutable result for membership and context queries.</summary>
    internal static SourceStream MaterializeSource(
        RepositorySnapshot snapshot, BackfillInventoryDocument ledger, string sourceId, AtomizedTheoryDocument? sourceDocument = null)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(ledger);
        var sources = ledger.RequireDigestionSources().Where(source => source.SourceId == sourceId).ToArray();
        if (sources.Length != 1)
            throw new DigestionAtomContextException(DigestionAtomContextError.SOURCE_MISSING,
                $"source_id={sourceId}");
        var source = sources[0];
        if (!snapshot.TryGetFile(source.SourcePath, out var file))
            throw new DigestionAtomContextException(DigestionAtomContextError.SOURCE_MISSING,
                $"source_id={source.SourceId} source_path={source.SourcePath}");
        if (!AtomizerRegistry.IsRegistered(source.Atomizer))
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOMIZER_UNSUPPORTED,
                $"unsupported atomizer: {source.Atomizer}; expected generic-v1");
        try
        {
            DigestionSourceEligibility.Require(snapshot, source.SourcePath);
            var atomizer = AtomizerRegistry.Require(source.Atomizer).Atomize;
            var document = sourceDocument ?? atomizer(file.RawBytes.AsSpan());
            var entries = ledger.RequireDigestionEntries();
            var byAtomId = entries.ToLookup(static entry => entry.AtomId, StringComparer.Ordinal);
            var byId = byAtomId
                .Where(static group => group.Count() == 1)
                .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);
            var text = Encoding.UTF8.GetString(file.RawBytes.AsSpan());
            var blocks = MarkdigBlockAst.ParseOwned(text);
            var rootIds = SourceReferenceRootIds(document.Claims, file.RawBytes, text);
            rootIds.UnionWith(entries.Where(entry => entry.SourceId == sourceId).Select(static entry => entry.AtomId));
            var referenceIds = new HashSet<string>(rootIds, StringComparer.Ordinal);
            var pending = new Stack<string>(rootIds);
            while (pending.TryPop(out var id))
                if (byId.TryGetValue(id, out var entry))
                    foreach (var child in entry.Receipts.ChainAtoms)
                        if (referenceIds.Add(child)) pending.Push(child);
            // Identity lookup must obey the same root/reference authority as root
            // selection, including fresh gaps in a whole-source fallback.
            var byHash = entries.Where(entry => referenceIds.Contains(entry.AtomId))
                .ToLookup(static entry => entry.Fingerprints.RawSha256, StringComparer.Ordinal);
            var roots = HistoricalRoots(document.Claims, file.RawBytes,
                byId.Values.Where(entry => rootIds.Contains(entry.AtomId)), snapshot, text, blocks);
            var stream = MaterializedStream(roots, byHash, byId, atomizer, snapshot, out var spans);
            return new SourceStream(source, stream, spans, byHash, byAtomId, file.RawBytes, text, blocks);
        }
        catch (Exception error) when (error is FormatException or InvalidOperationException or ArgumentException)
        {
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING, error.Message);
        }
    }

    internal sealed class SourceStream(
        DigestionLedgerSource source,
        ImmutableArray<DigestionAtom> stream,
        ImmutableArray<DigestionAtom> spans,
        ILookup<string, DigestionLedgerEntry> byHash,
        ILookup<string, DigestionLedgerEntry> byAtomId,
        ImmutableArray<byte> sourceBytes,
        string sourceText,
        ImmutableArray<MarkdownBlock> blocks)
    {
        internal string SourceId => source.SourceId;
        internal string SourcePath => source.SourcePath;
        internal string Atomizer => source.Atomizer;
        internal ImmutableArray<DigestionAtom> Atoms => stream;
        internal ImmutableArray<string> AtomIds { get; } =
            [.. stream.Select(atom => FindEntry(atom, byHash)?.AtomId ?? atom.Fingerprints.RawSha256[7..])];

        internal DigestionAtomContext ResolveAt(int streamIndex)
        {
            if (streamIndex < 0 || streamIndex >= stream.Length)
                throw new ArgumentOutOfRangeException(nameof(streamIndex));
            var atom = stream[streamIndex];
            var target = FindEntry(atom, byHash)
                ?? throw new DigestionAtomContextException(DigestionAtomContextError.ATOM_ABSENT,
                    $"atom_id={atom.Fingerprints.RawSha256[7..]}");
            return ContextAt(atom, streamIndex, target);
        }

        internal IEnumerable<(string AtomId, DigestionAtomContext Context)> PersistedContexts()
        {
            foreach (var atom in spans)
            {
                var entry = FindEntry(atom, byHash) ?? new DigestionLedgerEntry(
                    source.SourceId, source.SourcePath, source.Atomizer, atom.Fingerprints.RawSha256[7..],
                    atom.Fingerprints, [], new DigestionReceipts([], [], null),
                    new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open), atom.Fingerprints.RawSha256);
                yield return (entry.AtomId, ContextAt(atom, StreamIndexBefore(atom.StartByte), entry));
            }
        }

        internal DigestionAtomContext ContextForStoredSpan(DigestionLedgerEntry entry, DigestionAtom atom) =>
            ContextAt(atom, StreamIndexBefore(atom.StartByte), entry);

        internal ImmutableArray<DigestionGoverningContext> GoverningAt(int streamIndex)
        {
            if (streamIndex < 0 || streamIndex >= stream.Length)
                throw new ArgumentOutOfRangeException(nameof(streamIndex));
            return GoverningAt(stream[streamIndex]);
        }

        internal ImmutableArray<DigestionAtomContext> ResolveOccurrences(string atomId)
        {
            ValidateAtomId(atomId);
            var target = RequireTarget(byAtomId[atomId], atomId);
            try
            {
                var matches = spans.Where(atom => target.SourceId == source.SourceId
                    && atom.Fingerprints.RawSha256 == target.Fingerprints.RawSha256).ToArray();
                if (matches.Length == 0)
                    throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING,
                        $"atom_id={atomId} source_id={source.SourceId}");
                var contexts = ImmutableArray.CreateBuilder<DigestionAtomContext>(matches.Length);
                foreach (var atom in matches)
                {
                    // Collapse only this occurrence's subtree. Ordinary leaf membership and
                    // its neighbors remain unchanged; parent neighbors lie outside its span.
                    contexts.Add(ContextAt(atom, StreamIndexBefore(atom.StartByte), target));
                }
                return contexts.ToImmutable();
            }
            catch (Exception error) when (error is FormatException or InvalidOperationException or ArgumentException)
            {
                throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING, error.Message);
            }
        }

        private DigestionAtomContext ContextAt(DigestionAtom atom, int streamIndex, DigestionLedgerEntry target) =>
            new(
                target,
                streamIndex == 0 ? null : Neighbor(stream[streamIndex - 1], byHash),
                Neighbor(atom, byHash),
                NextIndex(atom.EndByte) >= stream.Length ? null : Neighbor(stream[NextIndex(atom.EndByte)], byHash),
                streamIndex + 1,
                streamIndex + 1 + stream.Length - NextIndex(atom.EndByte),
                source.SourceId,
                source.SourcePath,
                source.Atomizer)
            {
                GoverningContext = GoverningAt(atom),
                StartByte = atom.StartByte,
                EndByte = atom.EndByte,
                PreviousStartByte = streamIndex == 0 ? null : stream[streamIndex - 1].StartByte,
                NextStartByte = NextIndex(atom.EndByte) >= stream.Length ? null : stream[NextIndex(atom.EndByte)].StartByte,
            };

        private readonly Lazy<IReadOnlyDictionary<int, int>> governingOffsets = new(() => GoverningOffsets(sourceText, blocks));

        private readonly Lazy<ImmutableArray<DigestionAtom>> governingScopes = new(() =>
            GenericAtomizer.AtomizeStructure(sourceBytes.AsSpan(), parse: _ => blocks).Claims);

        private ImmutableArray<DigestionGoverningContext> GoverningAt(DigestionAtom atom) =>
            GoverningContext(sourceBytes, atom, sourceText, blocks, governingScopes.Value, governingOffsets.Value);

        private int StreamIndexBefore(int startByte)
        {
            var low = 0;
            var high = stream.Length;
            while (low < high)
            {
                var middle = low + ((high - low) / 2);
                if (stream[middle].EndByte <= startByte) low = middle + 1;
                else high = middle;
            }
            return low;
        }

        private int NextIndex(int startByte)
        {
            var low = 0;
            var high = stream.Length;
            while (low < high)
            {
                var middle = low + ((high - low) / 2);
                if (stream[middle].StartByte < startByte) low = middle + 1;
                else high = middle;
            }
            return low;
        }
    }

    private static ImmutableArray<DigestionAtom> MaterializedStream(
        ImmutableArray<DigestionAtom> roots,
        ILookup<string, DigestionLedgerEntry> byHash,
        IReadOnlyDictionary<string, DigestionLedgerEntry> byId,
        TheoryAtomizer atomizer,
        RepositorySnapshot snapshot,
        out ImmutableArray<DigestionAtom> spans)
    {
        var stream = ImmutableArray.CreateBuilder<DigestionAtom>();
        var occurrences = ImmutableArray.CreateBuilder<DigestionAtom>();
        var pending = new Stack<DigestionAtom>(roots.OrderByDescending(static atom => atom.StartByte));
        while (pending.TryPop(out var atom))
        {
            occurrences.Add(atom);
            var entry = FindEntry(atom, byHash);
            if (entry is null || entry.Receipts.ChainAtoms.IsEmpty)
            {
                if (stream.Count > 0 && stream[^1].EndByte > atom.StartByte)
                    throw new FormatException("materialized source spans overlap");
                stream.Add(atom);
                continue;
            }

            var plan = DigestionDecomposition.Plan(entry, atom.RawBytes, atomizer, snapshot);
            var materialized = DigestionDecomposition.Materialize(entry, plan, byId);
            if (!materialized.NewEntries.IsEmpty)
                throw new FormatException($"chain atom is absent for parent {entry.AtomId}");

            // CAS plans use local offsets; emitted plans already use source offsets.
            // Proper subspans strictly shrink, so nested chains terminate without a depth cap.
            var offset = atom.StartByte - plan.Parent.StartByte;
            // Structural gaps are validated by Plan and displayed as work context.
            // Only claims are neighbor leaves, as in a scoped fresh-source query.
            foreach (var child in plan.Children.Reverse())
            {
                pending.Push(child with
                {
                    StartByte = child.StartByte + offset,
                    EndByte = child.EndByte + offset,
                });
            }
        }
        spans = occurrences.ToImmutable();
        return stream.ToImmutable();
    }

    // Loaded historical CAS is inspected only in the selected source. Its actual
    // occurrences can span several freshly generated roots. Saved offsets identify version occurrences.
    private static ImmutableArray<DigestionAtom> HistoricalRoots(
        ImmutableArray<DigestionAtom> fresh, ImmutableArray<byte> sourceBytes,
        IEnumerable<DigestionLedgerEntry> entries, RepositorySnapshot snapshot,
        string sourceText, ImmutableArray<MarkdownBlock> blocks)
    {
        if (fresh.IsEmpty && !sourceBytes.IsEmpty)
            fresh = [DigestionAtom.FromFrozenCas(sourceBytes)];
        var historical = new List<DigestionAtom>();
        foreach (var entry in entries)
        {
            if (!snapshot.TryGetFile(DigestionCasStore.RootPath + entry.AtomId, out var blob)) continue;
            var frozen = DigestionAtom.FromFrozenCas(blob.RawBytes);
            if (entry.AtomId != frozen.Fingerprints.RawSha256[7..]
                || entry.CasRef != frozen.Fingerprints.RawSha256 || entry.Fingerprints != frozen.Fingerprints)
                throw new FormatException($"CAS_MISMATCH atom_id={entry.AtomId}");
            foreach (var start in OccurrenceStarts(sourceBytes, blob.RawBytes))
                historical.Add(frozen with { StartByte = start, EndByte = start + blob.RawBytes.Length });
        }
        var roots = historical.Where(atom => !historical.Any(other =>
            other.StartByte <= atom.StartByte && other.EndByte >= atom.EndByte
            && other.RawBytes.Length > atom.RawBytes.Length)).DistinctBy(atom => (atom.StartByte, atom.EndByte))
            .OrderBy(static atom => atom.StartByte).ToArray();
        // Independent historical cuts need not describe one common stream.
        // Keep only compatible roots. In crossing regions the observed source's
        // atomizer supplies the stream; inactive stored spans are captured only
        // when their endpoints fit that stream, never by inventing ancestry.
        roots = roots.Where(atom => !roots.Any(other =>
            other.StartByte != atom.StartByte && other.StartByte < atom.EndByte
            && atom.StartByte < other.EndByte)).ToArray();
        var tables = blocks.OfType<MarkdownGovernedBlock>()
            .Where(static block => block.Kind == "table")
            .Select(block => (Start: MarkdownAstAtomizer.ByteOffset(sourceText, block.Start),
                End: MarkdownAstAtomizer.ByteOffset(sourceText, block.End))).ToArray();
        var result = roots.ToList();
        foreach (var atom in fresh)
        {
            var cursor = atom.StartByte;
            foreach (var old in roots.Where(old => old.EndByte > atom.StartByte && old.StartByte < atom.EndByte))
            {
                if (old.StartByte > cursor) AddFresh(atom, cursor, old.StartByte);
                cursor = Math.Max(cursor, old.EndByte);
            }
            if (cursor < atom.EndByte) AddFresh(atom, cursor, atom.EndByte);
        }
        return [.. result.OrderBy(static atom => atom.StartByte)];

        void AddFresh(DigestionAtom atom, int start, int end)
        {
            var part = Subspan(atom, start, end);
            // A table row's closing pipe and the owner's following prose remain
            // governing context. Neither is an exterior leaf with a new identity.
            if (tables.Any(table => atom.StartByte <= table.Start && table.Start <= start && start <= table.End
                && part.RawBytes.Take(Math.Min(end, table.End) - start)
                    .All(static value => value is (byte)'|' or (byte)' ' or (byte)'\t' or (byte)'\r' or (byte)'\n')))
                return;
            result.Add(part);
        }

        static DigestionAtom Subspan(DigestionAtom atom, int start, int end)
        {
            if (start == atom.StartByte && end == atom.EndByte) return atom;
            var bytes = atom.RawBytes[(start - atom.StartByte)..(end - atom.StartByte)];
            return DigestionAtom.FromFrozenCas(bytes) with { StartByte = start, EndByte = end, Context = atom.Context };
        }
    }

    // Writer reference identities include fresh
    // claims, physical blocks/rows, and the definition/header before a table body.
    // Content identity may assign any of them to a different ledger source.
    internal static HashSet<string> SourceReferenceRootIds(ImmutableArray<DigestionAtom> fresh,
        ImmutableArray<byte> source, string text)
    {
        var ids = fresh.Select(static atom => atom.Fingerprints.RawSha256[7..]).ToHashSet(StringComparer.Ordinal);
        var leaves = MarkdigBlockAst.Parse(text);
        // Convert each required boundary once. Counting each prefix separately
        // repeats the source scan for every physical block and table row.
        var offsets = leaves.SelectMany(leaf => leaf is MarkdownTableRow
                ? new[] { leaf.Start, leaf.End, MarkdigBlockAst.LineEnd(text, leaf.End) }
                : new[] { leaf.Start, leaf.End })
            .Distinct().Order().ToArray();
        var byteOffsets = new Dictionary<int, int>();
        var utf8 = new UTF8Encoding(false, true);
        var characterCursor = 0;
        var byteCursor = 0;
        foreach (var offset in offsets)
        {
            byteCursor += utf8.GetByteCount(text.AsSpan(characterCursor, offset - characterCursor));
            byteOffsets.Add(offset, byteCursor);
            characterCursor = offset;
        }
        for (var index = 0; index < leaves.Length; index++)
        {
            var leaf = leaves[index];
            var start = byteOffsets[leaf.Start];
            Add(start, byteOffsets[leaf.End]);
            if (leaf is not MarkdownTableRow row) continue;
            Add(start, byteOffsets[MarkdigBlockAst.LineEnd(text, leaf.End)]);
            if (row.IsHeader || index > 0 && leaves[index - 1] is MarkdownTableRow { IsHeader: false }) continue;
            var owner = fresh.FirstOrDefault(atom => atom.StartByte < start && atom.EndByte > start);
            if (owner is not null) Add(owner.StartByte, start);
        }
        return ids;

        void Add(int start, int end) => ids.Add(DigestionFingerprint.Compute(source.AsSpan()[start..end]).RawSha256[7..]);
    }

    internal static IEnumerable<int> OccurrenceStarts(ImmutableArray<byte> source, ImmutableArray<byte> fragment)
    {
        if (fragment.IsEmpty) yield break;
        var cursor = 0;
        while (cursor <= source.Length - fragment.Length)
        {
            var relative = source.AsSpan()[cursor..].IndexOf(fragment.AsSpan());
            if (relative < 0) yield break;
            var start = cursor + relative;
            yield return start;
            cursor = start + 1;
        }
    }

    private static IReadOnlyDictionary<int, int> GoverningOffsets(string text, ImmutableArray<MarkdownBlock> blocks)
    {
        var positions = blocks.OfType<MarkdownHeading>().SelectMany(heading =>
                new[] { heading.Start, MarkdigBlockAst.LineEnd(text, heading.End) })
            .Concat(blocks.OfType<MarkdownGovernedBlock>().SelectMany(block =>
                new[] { block.Start, block.End, block.LeadStart }))
            .Distinct().Order().ToArray();
        var result = new Dictionary<int, int>();
        var cursor = 0;
        var bytes = 0;
        foreach (var position in positions)
        {
            bytes += Encoding.UTF8.GetByteCount(text.AsSpan(cursor, position - cursor));
            result[position] = bytes;
            cursor = position;
        }
        return result;
    }

    private static ImmutableArray<DigestionGoverningContext> GoverningContext(
        ImmutableArray<byte> sourceBytes, DigestionAtom atom, string text,
        ImmutableArray<MarkdownBlock> blocks, ImmutableArray<DigestionAtom> scopes, IReadOnlyDictionary<int, int> offsets)
    {
        var headings = new List<MarkdownHeading>();
        foreach (var heading in blocks.OfType<MarkdownHeading>())
        {
            if (offsets[heading.Start] > atom.StartByte) break;
            while (headings.Count > 0 && headings[^1].Level >= heading.Level) headings.RemoveAt(headings.Count - 1);
            headings.Add(heading);
        }
        var context = ImmutableArray.CreateBuilder<DigestionGoverningContext>();
        foreach (var heading in headings) Add("heading", heading.Start, MarkdigBlockAst.LineEnd(text, heading.End));
        var scope = scopes
            .Where(root => root.StartByte <= atom.StartByte && root.EndByte >= atom.EndByte)
            .OrderBy(static root => root.RawBytes.Length).FirstOrDefault();
        foreach (var structure in blocks.OfType<MarkdownGovernedBlock>())
        {
            var start = offsets[structure.Start];
            var end = offsets[structure.End];
            if (start >= atom.EndByte || end <= atom.StartByte) continue;
            var leadStart = structure.Kind == "table" && scope is not null
                ? scope.StartByte : offsets[structure.LeadStart];
            AddBytes(structure.Kind == "table" ? "table-definition" : "governed-list", leadStart, end);
        }
        if (scope is not null && scope.RawBytes.Length > atom.RawBytes.Length)
            AddBytes("enclosing-scope", scope.StartByte, scope.EndByte);
        return context.ToImmutable();

        void Add(string relation, int start, int end) =>
            AddBytes(relation, offsets[start], offsets[end]);
        void AddBytes(string relation, int start, int end)
        {
            if (start == atom.StartByte && end == atom.EndByte) return;
            context.Add(new DigestionGoverningContext(relation, sourceBytes[start..end]));
        }
    }

    private static DigestionLedgerEntry? FindEntry(DigestionAtom atom, ILookup<string, DigestionLedgerEntry> byHash)
    {
        var matches = byHash[atom.Fingerprints.RawSha256].ToArray();
        if (matches.Length > 1)
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOM_AMBIGUOUS,
                $"raw_sha256={atom.Fingerprints.RawSha256}");
        return matches.SingleOrDefault();
    }

    private static (string AtomId, string? LedgerState, ImmutableArray<byte> RawBytes) Neighbor(
        DigestionAtom atom, ILookup<string, DigestionLedgerEntry> byHash)
    {
        var entry = FindEntry(atom, byHash);
        return (entry?.AtomId ?? atom.Fingerprints.RawSha256[7..],
            entry is null ? null : DigestionStatusNames.Migration(entry.ProjectedStatus.Migration) + "-"
                + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth), atom.RawBytes);
    }
}
