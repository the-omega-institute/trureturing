using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum DigestionAtomContextError
{
    ARGUMENTS_INVALID,
    ATOM_ABSENT,
    ATOM_AMBIGUOUS,
    SOURCE_MISSING,
    ATOMIZER_NONE,
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
    internal string? PreviousBoundaryReason => Previous is null ? "source-start" : null;
    internal string? NextBoundaryReason => Next is null ? "source-end" : null;
}

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
        RepositorySnapshot snapshot, BackfillInventoryDocument ledger, string atomId)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(ledger);
        var target = RequireTarget(ledger.RequireDigestionEntries(), atomId);
        try
        {
            return MaterializeSource(snapshot, ledger, target.SourceId).ResolveOccurrences(atomId);
        }
        catch (DigestionAtomContextException error) when (error.Code == DigestionAtomContextError.SOURCE_MISSING)
        {
            // Legacy diagnostics name the ledger target's path, even if source metadata differs.
            throw new DigestionAtomContextException(DigestionAtomContextError.SOURCE_MISSING,
                $"source_id={target.SourceId} source_path={target.SourcePath}");
        }
    }

    private static DigestionLedgerEntry RequireTarget(IEnumerable<DigestionLedgerEntry> entries, string atomId)
    {
        if (string.IsNullOrWhiteSpace(atomId) || !DigestionFingerprint.IsCanonicalSha256("sha256:" + atomId))
            throw new DigestionAtomContextException(DigestionAtomContextError.ARGUMENTS_INVALID,
                "atom_id must be 64 lowercase hexadecimal characters");
        var targets = entries.Where(entry => entry.AtomId == atomId).ToArray();
        if (targets.Length == 0)
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOM_ABSENT, $"atom_id={atomId}");
        if (targets.Length != 1)
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOM_AMBIGUOUS, $"atom_id={atomId}");
        return targets[0];
    }

    /// <summary>Materializes a source once; callers retain the immutable result for membership and context queries.</summary>
    internal static SourceStream MaterializeSource(
        RepositorySnapshot snapshot, BackfillInventoryDocument ledger, string sourceId)
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
        if (source.Atomizer == AtomizerRegistry.NoAtomizerId)
            throw new DigestionAtomContextException(DigestionAtomContextError.ATOMIZER_NONE,
                $"source_id={source.SourceId}");
        try
        {
            var rules = TheoryAtomizerDataLoader.Load(snapshot);
            var atomizer = AtomizerRegistry.Require(source.Atomizer).Atomize;
            var document = atomizer(file.RawBytes.AsSpan(), rules);
            var entries = ledger.RequireDigestionEntries();
            var byHash = entries.ToLookup(static entry => entry.Fingerprints.RawSha256, StringComparer.Ordinal);
            var byAtomId = entries.ToLookup(static entry => entry.AtomId, StringComparer.Ordinal);
            var byId = byAtomId
                .Where(static group => group.Count() == 1)
                .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);
            var stream = MaterializedStream(document, byHash, byId, atomizer, rules);
            return new SourceStream(source, stream, byHash, byAtomId);
        }
        catch (Exception error) when (error is FormatException or InvalidOperationException or ArgumentException)
        {
            throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING, error.Message);
        }
    }

    internal sealed class SourceStream(
        DigestionLedgerSource source,
        ImmutableArray<DigestionAtom> stream,
        ILookup<string, DigestionLedgerEntry> byHash,
        ILookup<string, DigestionLedgerEntry> byAtomId)
    {
        internal string SourceId => source.SourceId;
        internal string SourcePath => source.SourcePath;
        internal string Atomizer => source.Atomizer;
        internal ImmutableArray<DigestionAtom> Atoms => stream;
        internal ImmutableArray<string> AtomIds { get; } =
            [.. stream.Select(atom => Neighbor(atom, byHash).AtomId)];

        internal ImmutableArray<DigestionAtomContext> ResolveOccurrences(string atomId)
        {
            var target = RequireTarget(byAtomId[atomId], atomId);
            var matches = Enumerable.Range(0, stream.Length)
                .Where(index => target.SourceId == source.SourceId
                    && stream[index].Fingerprints.RawSha256 == target.Fingerprints.RawSha256).ToArray();
            if (matches.Length == 0)
                throw new DigestionAtomContextException(DigestionAtomContextError.OCCURRENCE_MISSING,
                    $"atom_id={atomId} source_id={source.SourceId}");
            var contexts = ImmutableArray.CreateBuilder<DigestionAtomContext>(matches.Length);
            foreach (var position in matches)
                contexts.Add(new DigestionAtomContext(target,
                    position == 0 ? null : Neighbor(stream[position - 1], byHash),
                    Neighbor(stream[position], byHash),
                    position + 1 == stream.Length ? null : Neighbor(stream[position + 1], byHash),
                    position + 1, stream.Length, source.SourceId, source.SourcePath, source.Atomizer));
            return contexts.ToImmutable();
        }
    }

    private static ImmutableArray<DigestionAtom> MaterializedStream(
        AtomizedTheoryDocument document,
        ILookup<string, DigestionLedgerEntry> byHash,
        IReadOnlyDictionary<string, DigestionLedgerEntry> byId,
        TheoryAtomizer atomizer,
        TheoryAtomizerRules rules)
    {
        var stream = ImmutableArray.CreateBuilder<DigestionAtom>();
        var pending = new Stack<DigestionAtom>(document.Claims.OrderByDescending(static atom => atom.StartByte));
        while (pending.TryPop(out var atom))
        {
            var entry = FindEntry(atom, byHash);
            if (entry is null || entry.Receipts.ChainAtoms.IsEmpty)
            {
                if (stream.Count > 0 && stream[^1].EndByte > atom.StartByte)
                    throw new FormatException("materialized source spans overlap");
                stream.Add(atom);
                continue;
            }

            var emitted = document.ClausePlans.Where(plan => plan.Parent.StartByte == atom.StartByte
                && plan.Parent.EndByte == atom.EndByte && plan.Parent.Fingerprints == atom.Fingerprints).ToArray();
            if (emitted.Length > 1) throw new FormatException("duplicate clause plans for source span");
            var plan = emitted.SingleOrDefault()
                ?? DigestionDecomposition.Plan(entry, atom.RawBytes, atomizer, rules);
            var materialized = DigestionDecomposition.Materialize(entry, plan, byId);
            if (!materialized.NewEntries.IsEmpty)
                throw new FormatException($"chain atom is absent for parent {entry.AtomId}");

            // CAS plans use local offsets; emitted plans already use source offsets.
            // Proper subspans strictly shrink, so nested chains terminate without a depth cap.
            var offset = atom.StartByte - plan.Parent.StartByte;
            foreach (var segment in plan.Segments.Reverse())
            {
                pending.Push(segment.Atom with
                {
                    StartByte = segment.Atom.StartByte + offset,
                    EndByte = segment.Atom.EndByte + offset,
                });
            }
        }
        return stream.ToImmutable();
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
