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
            return MaterializeSource(snapshot, ledger, target.SourceId, sourceDocument).ResolveOccurrences(atomId);
        }
        catch (DigestionAtomContextException error) when (error.Code == DigestionAtomContextError.SOURCE_MISSING)
        {
            // Legacy diagnostics name the ledger target's path, even if source metadata differs.
            throw new DigestionAtomContextException(DigestionAtomContextError.SOURCE_MISSING,
                $"source_id={target.SourceId} source_path={target.SourcePath}");
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
                var scopes = GenericAtomizer.AtomizeStructure(sourceBytes.AsSpan(), parse: _ => blocks).Claims;
                foreach (var atom in matches)
                {
                    // Collapse only this occurrence's subtree. Ordinary leaf membership and
                    // its neighbors remain unchanged; parent neighbors lie outside its span.
                    var before = stream.TakeWhile(leaf => leaf.EndByte <= atom.StartByte).Count();
                    var after = stream.SkipWhile(leaf => leaf.StartByte < atom.EndByte).ToArray();
                    contexts.Add(new DigestionAtomContext(target,
                        before == 0 ? null : Neighbor(stream[before - 1], byHash),
                        Neighbor(atom, byHash),
                        after.Length == 0 ? null : Neighbor(after[0], byHash),
                        before + 1, before + 1 + after.Length,
                        source.SourceId, source.SourcePath, source.Atomizer)
                    {
                        GoverningContext = GoverningContext(sourceBytes, atom, sourceText, blocks, scopes),
                    });
                }
                return contexts.ToImmutable();
            }
            catch (Exception error) when (error is FormatException or InvalidOperationException or ArgumentException)
            {
                throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING, error.Message);
            }
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
    // occurrences can span several freshly generated roots. No offsets are persisted.
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
        for (var index = 1; index < roots.Length; index++)
            if (roots[index - 1].EndByte > roots[index].StartByte)
                throw new FormatException("historical source spans overlap without ancestry");
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

    // These are the source identities resolved globally by ReadContext: fresh
    // claims, physical blocks/rows, and the definition/header before a table body.
    // Content identity may assign any of them to a different ledger source.
    private static HashSet<string> SourceReferenceRootIds(ImmutableArray<DigestionAtom> fresh,
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

    // Discovery retains containing roots for their graph references, as well as
    // nearest exterior/crossing roots. Only Plan's claim leaves become neighbors.
    internal static HashSet<string> HistoricalNeighborIds(ImmutableArray<byte> source,
        ImmutableArray<byte> target, IEnumerable<(string AtomId, ImmutableArray<byte> RawBytes)> candidates)
    {
        var targets = OccurrenceStarts(source, target).Select(start => (Start: start, End: start + target.Length)).ToArray();
        var spans = candidates.SelectMany(candidate => OccurrenceStarts(source, candidate.RawBytes)
            .Select(start => (candidate.AtomId, Start: start, End: start + candidate.RawBytes.Length))).ToArray();
        var result = new HashSet<string>(StringComparer.Ordinal);
        foreach (var occurrence in targets)
        {
            foreach (var span in spans.Where(span => span.Start <= occurrence.Start && span.End >= occurrence.End))
                result.Add(span.AtomId);
            var previous = spans.Where(span => span.End <= occurrence.Start)
                .OrderByDescending(static span => span.End).ThenBy(static span => span.Start).FirstOrDefault();
            var next = spans.Where(span => span.Start >= occurrence.End)
                .OrderBy(static span => span.Start).ThenByDescending(static span => span.End).FirstOrDefault();
            if (previous.AtomId is not null) result.Add(previous.AtomId);
            if (next.AtomId is not null) result.Add(next.AtomId);
            // Crossing historical spans must reach the projection's existing overlap
            // rejection rather than disappear because their boundaries are not fresh.
            foreach (var span in spans.Where(span => span.Start < occurrence.End && span.End > occurrence.Start
                && !(span.Start <= occurrence.Start && span.End >= occurrence.End)
                && !(span.Start >= occurrence.Start && span.End <= occurrence.End)))
                result.Add(span.AtomId);
        }
        return result;
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

    private static ImmutableArray<DigestionGoverningContext> GoverningContext(
        ImmutableArray<byte> sourceBytes, DigestionAtom atom, string text,
        ImmutableArray<MarkdownBlock> blocks, ImmutableArray<DigestionAtom> scopes)
    {
        var headings = new List<MarkdownHeading>();
        foreach (var heading in blocks.OfType<MarkdownHeading>())
        {
            if (MarkdownAstAtomizer.ByteOffset(text, heading.Start) > atom.StartByte) break;
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
            var start = MarkdownAstAtomizer.ByteOffset(text, structure.Start);
            var end = MarkdownAstAtomizer.ByteOffset(text, structure.End);
            if (start >= atom.EndByte || end <= atom.StartByte) continue;
            var leadStart = structure.Kind == "table" && scope is not null
                ? scope.StartByte : MarkdownAstAtomizer.ByteOffset(text, structure.LeadStart);
            AddBytes(structure.Kind == "table" ? "table-definition" : "governed-list", leadStart, end);
        }
        if (scope is not null && scope.RawBytes.Length > atom.RawBytes.Length)
            AddBytes("enclosing-scope", scope.StartByte, scope.EndByte);
        return context.ToImmutable();

        void Add(string relation, int start, int end) =>
            AddBytes(relation, MarkdownAstAtomizer.ByteOffset(text, start), MarkdownAstAtomizer.ByteOffset(text, end));
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
