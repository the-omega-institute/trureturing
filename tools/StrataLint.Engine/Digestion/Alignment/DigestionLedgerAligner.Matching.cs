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
        BackfillInventoryDocument? baselineDocument,
        IReadOnlySet<string> statusIndependentAtomIds) =>
        (baselineDocument?.RequireDigestionSources() ?? [])
            .SelectMany(source => source.Entries.Select(entry => CanonicalEntry(
                source,
                entry,
                statusIndependentAtomIds)))
            .ToHashSet(StringComparer.Ordinal);

    private static bool ContentWideIdentityEqual(
        DigestionLedgerEntry candidate,
        DigestionLedgerEntry baseline) =>
        candidate.SourceId == baseline.SourceId
        && candidate.AtomId == baseline.AtomId
        && candidate.Fingerprints == baseline.Fingerprints
        && candidate.CasRef == baseline.CasRef;

    private static DigestionLedgerEntry[] ContentWideReplacementObligations(
        DigestionLedgerSource baseline,
        DigestionLedgerSource? candidate,
        RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(baseline.SourcePath, out var sourceFile))
        {
            return [];
        }

        var contentWide = DigestionFingerprint.ComputeOpaque(sourceFile.RawBytes.AsSpan());
        return baseline.Entries.Where(entry =>
            entry.AtomId == contentWide.RawSha256["sha256:".Length..]
            && entry.Fingerprints == contentWide
            && entry.CasRef == contentWide.RawSha256
            && (candidate is null
                || !candidate.Entries.Any(candidateEntry =>
                    ContentWideIdentityEqual(candidateEntry, entry))
                || baseline.AcknowledgedStale.Contains(entry.AtomId, StringComparer.Ordinal)
                || baseline.Atomizer != candidate.Atomizer
                || HasContentWideReplacementReceipt(candidate, entry)
                || candidate.AcknowledgedStale.Contains(entry.AtomId, StringComparer.Ordinal)))
            .ToArray();
    }

    private static bool HasContentWideReplacementReceipt(
        DigestionLedgerSource source,
        DigestionLedgerEntry contentWideEntry) =>
        AtomizerRegistry.IsRegistered(source.Atomizer)
        && source.Entries.Any(entry =>
            entry.Fingerprints.RawSha256 != contentWideEntry.Fingerprints.RawSha256);

    internal static bool FingerprintsMatch(DigestionFingerprints left, DigestionFingerprints right) =>
        left.RawSha256 == right.RawSha256
        || left.NormalizedSha256 == right.NormalizedSha256;

}
