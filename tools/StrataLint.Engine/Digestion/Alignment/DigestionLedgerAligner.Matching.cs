using System.Collections.Immutable;
using System.Text;

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
            .SelectMany(static source => source.Entries.Select(CanonicalEntry))
            .ToHashSet(StringComparer.Ordinal);

    private static ImmutableHashSet<DigestionReplayConfirmationObligation> ReplayConfirmationObligations(
        IEnumerable<DigestionLedgerSource> candidateSources,
        IReadOnlyDictionary<string, DigestionLedgerSource> baselineSources)
    {
        var obligations = ImmutableHashSet.CreateBuilder<DigestionReplayConfirmationObligation>();
        foreach (var candidateSource in candidateSources)
        {
            if (!baselineSources.TryGetValue(candidateSource.SourceId, out var baselineSource))
            {
                continue;
            }

            var baselineByIdentity = baselineSource.Entries
                .GroupBy(CanonicalEntry, StringComparer.Ordinal)
                .ToDictionary(static group => group.Key, static group => group.ToArray(), StringComparer.Ordinal);
            foreach (var candidateEntry in candidateSource.Entries)
            {
                if (!baselineByIdentity.TryGetValue(CanonicalEntry(candidateEntry), out var matches)
                    || matches.Any(baselineEntry => LegacyStatusIdentityMatches(
                        candidateSource,
                        candidateEntry,
                        baselineSource,
                        baselineEntry)))
                {
                    continue;
                }

                obligations.Add(new DigestionReplayConfirmationObligation(
                    candidateSource.SourceId,
                    candidateEntry.AtomId));
            }
        }

        return obligations.ToImmutable();
    }

    private static bool LegacyStatusIdentityMatches(
        DigestionLedgerSource candidateSource,
        DigestionLedgerEntry candidateEntry,
        DigestionLedgerSource baselineSource,
        DigestionLedgerEntry baselineEntry)
    {
        var candidateAcknowledged = candidateSource.AcknowledgedStale.Contains(
            candidateEntry.AtomId,
            StringComparer.Ordinal);
        var baselineAcknowledged = baselineSource.AcknowledgedStale.Contains(
            baselineEntry.AtomId,
            StringComparer.Ordinal);
        return (candidateAcknowledged, baselineAcknowledged) switch
        {
            (true, true) => true,
            (false, false) => candidateEntry.ProjectedStatus == baselineEntry.ProjectedStatus,
            (true, false) => baselineEntry.ProjectedStatus == StructuralIdentityStatus,
            (false, true) => candidateEntry.ProjectedStatus == StructuralIdentityStatus,
        };
    }

    internal static bool RequiresReplayRejection(
        bool casValid,
        DigestionReceiptAlignment alignment,
        bool confirmationRequired,
        bool contentWide,
        bool clauseChainChild,
        bool fingerprintConfirmed) =>
        casValid
        && alignment == DigestionReceiptAlignment.Seen
        && confirmationRequired
        && !contentWide
        && !clauseChainChild
        && !fingerprintConfirmed;

    private static void ApplyReplayConfirmation(
        DigestionLedgerSource source,
        IReadOnlySet<string> validAtomIds,
        IDictionary<string, DigestionReceiptAlignment> alignments,
        IReadOnlyDictionary<string, DigestionAtom> matchedAtoms,
        IReadOnlySet<DigestionReplayConfirmationObligation> obligations,
        DigestionLedgerEntry? contentWideEntry,
        IReadOnlySet<string> clauseChainChildIds,
        IEnumerable<DigestionAtom> replayedAtoms)
    {
        var replayed = replayedAtoms.ToArray();
        foreach (var entry in source.Entries)
        {
            if (RequiresReplayRejection(
                    validAtomIds.Contains(entry.AtomId),
                    alignments[entry.AtomId],
                    obligations.Contains(new DigestionReplayConfirmationObligation(
                        source.SourceId,
                        entry.AtomId)),
                    entry.AtomId == contentWideEntry?.AtomId,
                    clauseChainChildIds.Contains(entry.AtomId),
                    ReplayConfirmsEntry(entry, matchedAtoms, replayed)))
            {
                alignments[entry.AtomId] = DigestionReceiptAlignment.Rejected;
            }
        }
    }

    private static bool ReplayConfirmsEntry(
        DigestionLedgerEntry entry,
        IReadOnlyDictionary<string, DigestionAtom> matchedAtoms,
        IReadOnlyList<DigestionAtom> replayedAtoms)
    {
        if (replayedAtoms.Any(atom => FingerprintsMatch(entry.Fingerprints, atom.Fingerprints)))
        {
            return true;
        }

        return matchedAtoms.TryGetValue(entry.AtomId, out var storedAtom)
            && replayedAtoms.Any(atom =>
                atom.RawBytes.AsSpan().IndexOf(storedAtom.RawBytes.AsSpan()) >= 0
                || ReplayPreservesHistoricalHeadingAndBody(storedAtom.RawBytes, atom.RawBytes));
    }

    private static bool ReplayPreservesHistoricalHeadingAndBody(
        ImmutableArray<byte> historicalBytes,
        ImmutableArray<byte> replayedBytes)
    {
        if (!TryReadCompleteBlocks(historicalBytes, out var historical)
            || !TryReadCompleteBlocks(replayedBytes, out var replayed)
            || historical.Length < 2
            || replayed.Length <= historical.Length
            || historical[0].Type != typeof(MarkdownHeading)
            || replayed[0] != historical[0])
        {
            return false;
        }

        var bodyLength = historical.Length - 1;
        for (var replayIndex = 2; replayIndex + bodyLength <= replayed.Length; replayIndex++)
        {
            var matches = true;
            for (var bodyIndex = 0; bodyIndex < bodyLength; bodyIndex++)
            {
                if (replayed[replayIndex + bodyIndex] == historical[bodyIndex + 1])
                {
                    continue;
                }

                matches = false;
                break;
            }

            if (matches)
            {
                return true;
            }
        }

        return false;
    }

    private static bool TryReadCompleteBlocks(
        ImmutableArray<byte> bytes,
        out ImmutableArray<ReplayBlock> identities)
    {
        string source;
        try
        {
            source = new UTF8Encoding(false, true).GetString(bytes.AsSpan());
        }
        catch (DecoderFallbackException)
        {
            identities = [];
            return false;
        }

        var blocks = MarkdownBlockAst.Parse(source);
        var result = ImmutableArray.CreateBuilder<ReplayBlock>(blocks.Length);
        var cursor = 0;
        foreach (var block in blocks)
        {
            if (!ContainsOnlySpacing(source.AsSpan(cursor, block.Start - cursor)))
            {
                identities = [];
                return false;
            }

            result.Add(new ReplayBlock(
                block.GetType(),
                source[block.Start..block.End].TrimEnd('\r', '\n')));
            cursor = block.End;
        }

        identities = result.ToImmutable();
        return identities.Length > 0
            && ContainsOnlySpacing(source.AsSpan(cursor));
    }

    private static bool ContainsOnlySpacing(ReadOnlySpan<char> value)
    {
        foreach (var character in value)
        {
            if (character is not (' ' or '\t' or '\r' or '\n'))
            {
                return false;
            }
        }

        return true;
    }

    private readonly record struct ReplayBlock(Type Type, string RawText);

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
