using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
    private static DigestionLedgerEntry? ContentWideEntry(
        DigestionLedgerSource source,
        ReadOnlySpan<byte> sourceBytes,
        IReadOnlySet<string> validAtomIds)
    {
        var fingerprints = DigestionFingerprint.ComputeOpaque(sourceBytes);
        var atomId = fingerprints.RawSha256["sha256:".Length..];
        return source.Entries.SingleOrDefault(entry =>
            entry.AtomId == atomId
            && validAtomIds.Contains(entry.AtomId)
            && entry.Fingerprints == fingerprints
            && entry.CasRef == fingerprints.RawSha256);
    }

    private static void AddCoarseFallback(
        DigestionLedgerSource source,
        ImmutableArray<byte> sourceBytes,
        string reason,
        IReadOnlySet<string> validAtomIds,
        ISet<string> suggestedAtomIds,
        ImmutableArray<StructuredResidualAdmission>.Builder residual,
        ImmutableArray<DigestionIngestFallback>.Builder fallbacks)
    {
        var fingerprints = DigestionFingerprint.ComputeOpaque(sourceBytes.AsSpan());
        fallbacks.Add(new DigestionIngestFallback(source.SourceId, reason));
        if (source.Entries.Any(entry =>
                validAtomIds.Contains(entry.AtomId)
                && entry.CasRef == fingerprints.RawSha256))
        {
            return;
        }

        var atom = new DigestionAtom(
            0,
            sourceBytes.Length,
            sourceBytes,
            fingerprints,
            []);
        residual.Add(new StructuredResidualAdmission(
            source.SourceId,
            source.SourcePath,
            source.Atomizer,
            atom,
            SuggestedAtomId(atom, suggestedAtomIds),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open)));
    }

    private static string SuggestedAtomId(
        DigestionAtom atom,
        ISet<string> suggestedAtomIds)
    {
        var atomId = atom.Fingerprints.RawSha256["sha256:".Length..];
        suggestedAtomIds.Add(atomId);
        return atomId;
    }

    internal static bool FingerprintsMatch(DigestionFingerprints left, DigestionFingerprints right) =>
        left.RawSha256 == right.RawSha256
        || left.NormalizedSha256 == right.NormalizedSha256;

    // Atomizer data and implementations reach every source at once.  The
    // digestion path has its own stable input boundary; it does not consult
    // the engineering project registry to discover build inputs.
    private static bool AtomizerInputsChanged(RawChangeSet changes) =>
        changes.Paths.Any(path =>
            path.Value == TheoryAtomizerDataLoader.DataPath
            || path.Value.StartsWith("tools/StrataLint.Engine/Digestion/", StringComparison.Ordinal));

    private static bool SourceChanged(DigestionLedgerSource source, RawChangeSet changes)
    {
        if (source.Entries.Any(entry => DigestionCasStore.EntryChanged(entry, changes)))
        {
            return true;
        }

        var casPaths = source.Entries
            .Select(static entry => DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..])
            .ToHashSet(StringComparer.Ordinal);
        return changes.Paths.Any(path =>
            path.Value == source.SourcePath
            || casPaths.Contains(path.Value));
    }
}
