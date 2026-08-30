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

    private static Dictionary<string, DigestionLedgerSource> BaselineSources(
        BackfillInventoryDocument? baselineDocument,
        ImmutableArray<string>.Builder findings)
    {
        var result = new Dictionary<string, DigestionLedgerSource>(StringComparer.Ordinal);
        if (baselineDocument is null)
        {
            return result;
        }

        foreach (var source in baselineDocument.RequireDigestionSources())
        {
            if (!result.TryAdd(source.SourceId, source))
            {
                findings.Add($"baseline ledger contains duplicate source_id: {source.SourceId}");
            }
        }

        return result;
    }

    private static HashSet<string> InheritedEntries(
        BackfillInventoryDocument? baselineDocument) =>
        (baselineDocument?.RequireDigestionSources() ?? [])
            .SelectMany(source => source.Entries.Select(entry => CanonicalEntry(
                source,
                entry)))
            .ToHashSet(StringComparer.Ordinal);

    internal static bool FingerprintsMatch(DigestionFingerprints left, DigestionFingerprints right) =>
        left.RawSha256 == right.RawSha256
        || left.NormalizedSha256 == right.NormalizedSha256;

}
