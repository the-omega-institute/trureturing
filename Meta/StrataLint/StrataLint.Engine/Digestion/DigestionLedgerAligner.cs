using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal enum DigestionAlignmentMode
{
    Admission,
    Ingest,
}

internal enum DigestionReceiptAlignment
{
    LegacyBoundary,
    Seen,
    NormalizedSeen,
    Stale,
    Rejected,
}

internal static class DigestionReceiptAlignmentNames
{
    internal static string Render(DigestionReceiptAlignment value) => value switch
    {
        DigestionReceiptAlignment.LegacyBoundary => "legacy-boundary",
        DigestionReceiptAlignment.Seen => "seen",
        DigestionReceiptAlignment.NormalizedSeen => "normalized-seen",
        DigestionReceiptAlignment.Stale => "stale",
        DigestionReceiptAlignment.Rejected => "rejected",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
}

internal sealed record StructuredResidualAdmission(
    string SourceId,
    string SourcePath,
    string Atomizer,
    DigestionAtom Atom,
    string SuggestedAtomId,
    DigestionStatus ProjectedStatus);

internal sealed record DigestionIngestFallback(string SourceId, string Reason);

internal sealed record DigestionLedgerAlignment(
    ImmutableDictionary<string, DigestionReceiptAlignment> EntryAlignments,
    ImmutableDictionary<string, DigestionAtom> MatchedAtoms,
    ImmutableArray<StructuredResidualAdmission> Residual,
    ImmutableArray<DigestionIngestFallback> Fallbacks,
    ImmutableArray<string> ActualStale,
    ImmutableArray<string> Findings)
{
    internal DigestionReceiptAlignment AlignmentFor(string atomId) =>
        EntryAlignments.TryGetValue(atomId, out var alignment)
            ? alignment
            : throw new InvalidOperationException($"digestion alignment omitted entry {atomId}");
}

internal static class DigestionLedgerAligner
{
    internal static DigestionLedgerAlignment Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument? baselineDocument,
        DigestionAlignmentMode mode,
        Func<string, TheoryAtomizer>? atomizerResolver = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        atomizerResolver ??= static id => AtomizerRegistry.Require(id).Atomize;

        var alignments = ImmutableDictionary.CreateBuilder<string, DigestionReceiptAlignment>(
            StringComparer.Ordinal);
        var matchedAtoms = ImmutableDictionary.CreateBuilder<string, DigestionAtom>(
            StringComparer.Ordinal);
        var residual = ImmutableArray.CreateBuilder<StructuredResidualAdmission>();
        var fallbacks = ImmutableArray.CreateBuilder<DigestionIngestFallback>();
        var actualStale = ImmutableArray.CreateBuilder<string>();
        var findings = ImmutableArray.CreateBuilder<string>();
        var suggestedAtomIds = new HashSet<string>(StringComparer.Ordinal);
        var cas = DigestionCasStore.Evaluate(document, snapshot);
        findings.AddRange(cas.Findings);
        var baselineSources = BaselineSources(baselineDocument, findings);
        foreach (var source in document.RequireDigestionSources())
        {
            foreach (var entry in source.Entries.Where(static entry => entry.CasRef is not null))
            {
                alignments[entry.AtomId] = cas.ValidAtomIds.Contains(entry.AtomId)
                    ? DigestionReceiptAlignment.Seen
                    : DigestionReceiptAlignment.Rejected;
            }

            foreach (var entry in source.Entries.Where(static entry =>
                         entry.CasRef is null && entry.Boundary is not null))
            {
                alignments[entry.AtomId] = DigestionReceiptAlignment.LegacyBoundary;
            }

            var structuredEntries = source.Entries
                .Where(static entry => entry.CasRef is null && entry.Boundary is null)
                .ToArray();
            var registeredAtomizer = AtomizerRegistry.IsRegistered(source.Atomizer);
            if (structuredEntries.Length == 0
                && (mode == DigestionAlignmentMode.Admission || !registeredAtomizer))
            {
                continue;
            }

            if (!registeredAtomizer)
            {
                findings.Add(
                    $"source {source.SourceId} boundaryless receipts require a registered atomizer");
                MarkRejected(structuredEntries, alignments);
                continue;
            }

            if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
            {
                findings.Add($"source path is dangling: {source.SourcePath}");
                MarkRejected(structuredEntries, alignments);
                continue;
            }

            AtomizedTheoryDocument atomized;
            try
            {
                var atomize = atomizerResolver(source.Atomizer);
                atomized = atomize(sourceFile.RawBytes.AsSpan());
            }
            catch (Exception exception) when (
                exception is TheorySourceFormatException or DecoderFallbackException)
            {
                if (mode == DigestionAlignmentMode.Ingest && structuredEntries.Length == 0)
                {
                    AddCoarseFallback(
                        source,
                        sourceFile.RawBytes,
                        exception.Message,
                        cas.ValidAtomIds,
                        suggestedAtomIds,
                        residual,
                        fallbacks);
                    continue;
                }

                findings.Add($"source {source.SourceId} atomization failed: {exception.Message}");
                MarkRejected(structuredEntries, alignments);
                continue;
            }

            var integrityFailure = AtomizerIntegrityFailure(
                atomized,
                sourceFile.RawBytes.AsSpan());
            if (integrityFailure is not null)
            {
                findings.Add(
                    $"source {source.SourceId} atomizer integrity failed: {integrityFailure}");
                MarkRejected(structuredEntries, alignments);
                continue;
            }

            if (atomized.Claims.Length == 0)
            {
                if (mode == DigestionAlignmentMode.Ingest && structuredEntries.Length == 0)
                {
                    AddCoarseFallback(
                        source,
                        sourceFile.RawBytes,
                        "atomizer recognition is incomplete or empty",
                        cas.ValidAtomIds,
                        suggestedAtomIds,
                        residual,
                        fallbacks);
                    continue;
                }

                findings.Add($"source {source.SourceId} atomizer recognition is incomplete or empty");
                MarkRejected(structuredEntries, alignments);
                continue;
            }

            var claims = new Dictionary<string, DigestionAtom>(StringComparer.Ordinal);
            var duplicateAstPath = false;
            foreach (var atom in atomized.Claims)
            {
                if (claims.TryAdd(atom.AstPath, atom))
                {
                    continue;
                }

                findings.Add($"source {source.SourceId} duplicate atomized ast_path: {atom.AstPath}");
                duplicateAstPath = true;
            }

            if (duplicateAstPath)
            {
                MarkRejected(structuredEntries, alignments);
                continue;
            }

            baselineSources.TryGetValue(source.SourceId, out var baselineSource);
            var matchedAstPaths = new HashSet<string>(StringComparer.Ordinal);
            foreach (var legacy in source.Entries.Where(static entry => entry.Boundary is not null))
            {
                if (claims.TryGetValue(legacy.AstPath, out var atom)
                    && (atom.Fingerprints.RawSha256 == legacy.Fingerprints.RawSha256
                        || atom.Fingerprints.NormalizedSha256
                        == legacy.Fingerprints.NormalizedSha256))
                {
                    matchedAstPaths.Add(atom.AstPath);
                }
            }

            var sourceStale = new List<string>();
            foreach (var entry in structuredEntries)
            {
                if (claims.TryGetValue(entry.AstPath, out var atom)
                    && atom.Fingerprints.RawSha256 == entry.Fingerprints.RawSha256)
                {
                    alignments[entry.AtomId] = DigestionReceiptAlignment.Seen;
                    matchedAtoms[entry.AtomId] = atom;
                    matchedAstPaths.Add(atom.AstPath);
                    continue;
                }

                if (atom is not null
                    && atom.Fingerprints.NormalizedSha256 == entry.Fingerprints.NormalizedSha256)
                {
                    alignments[entry.AtomId] = DigestionReceiptAlignment.NormalizedSeen;
                    matchedAtoms[entry.AtomId] = atom;
                    matchedAstPaths.Add(atom.AstPath);
                    continue;
                }

                if (baselineSource is not null
                    && baselineSource.Entries.Any(baseline => EntryIdentityEqual(entry, baseline)))
                {
                    alignments[entry.AtomId] = DigestionReceiptAlignment.Stale;
                    sourceStale.Add(entry.AtomId);
                    actualStale.Add(entry.AtomId);
                    continue;
                }

                alignments[entry.AtomId] = DigestionReceiptAlignment.Rejected;
                findings.Add(
                    $"entry {entry.AtomId} fingerprint does not match ast_path {entry.AstPath} "
                    + "and has no matching baseline receipt identity");
            }

            var casOccurrences = source.Entries
                .Where(entry => entry.CasRef is not null
                    && cas.ValidAtomIds.Contains(entry.AtomId))
                .Select(static entry => (entry.AstPath, RawSha256: entry.CasRef!))
                .ToHashSet();
            foreach (var atom in atomized.Claims.Where(atom =>
                         casOccurrences.Contains((atom.AstPath, atom.Fingerprints.RawSha256))))
            {
                matchedAstPaths.Add(atom.AstPath);
            }

            var registration = AtomizerRegistry.Require(source.Atomizer);
            foreach (var atom in atomized.Claims.Where(atom => !matchedAstPaths.Contains(atom.AstPath)))
            {
                residual.Add(new StructuredResidualAdmission(
                    source.SourceId,
                    source.SourcePath,
                    source.Atomizer,
                    atom,
                    SuggestedAtomId(
                        source,
                        registration,
                        atom,
                        "residual",
                        suggestedAtomIds),
                    new DigestionStatus(
                        DigestionMigrationState.Residual,
                        DigestionTruthState.Open)));
            }

            if (mode == DigestionAlignmentMode.Admission)
            {
                var unacknowledged = sourceStale
                    .Except(source.AcknowledgedStale, StringComparer.Ordinal)
                    .Order(StringComparer.Ordinal)
                    .ToArray();
                if (unacknowledged.Length > 0)
                {
                    findings.Add(
                        $"source {source.SourceId} stale receipts are not acknowledged: "
                        + string.Join(", ", unacknowledged));
                }
            }
        }

        if (mode == DigestionAlignmentMode.Admission)
        {
            foreach (var item in residual)
            {
                findings.Add(
                    $"source {item.SourceId} has unregistered residual-open atom "
                    + $"{item.Atom.AstPath} ({item.SuggestedAtomId})");
            }
        }

        return new DigestionLedgerAlignment(
            alignments.ToImmutable(),
            matchedAtoms.ToImmutable(),
            residual.ToImmutable(),
            fallbacks.ToImmutable(),
            actualStale.Order(StringComparer.Ordinal).ToImmutableArray(),
            findings.Order(StringComparer.Ordinal).ToImmutableArray());
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
                && entry.AstPath == "coarse/source"
                && entry.CasRef == fingerprints.RawSha256))
        {
            return;
        }

        var atom = new DigestionAtom(
            "coarse/source",
            0,
            sourceBytes.Length,
            sourceBytes,
            fingerprints,
            []);
        var registration = AtomizerRegistry.Require(source.Atomizer);
        residual.Add(new StructuredResidualAdmission(
            source.SourceId,
            source.SourcePath,
            source.Atomizer,
            atom,
            SuggestedAtomId(source, registration, atom, "coarse", suggestedAtomIds),
            new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open)));
    }

    private static string SuggestedAtomId(
        DigestionLedgerSource source,
        AtomizerRegistration registration,
        DigestionAtom atom,
        string kind,
        ISet<string> suggestedAtomIds)
    {
        var stem = registration.ResidualPrefix
            + $"-{kind}-"
            + atom.Fingerprints.RawSha256["sha256:".Length..];
        if (suggestedAtomIds.Add(stem))
        {
            return stem;
        }

        var occurrenceBytes = Encoding.UTF8.GetBytes(source.SourceId + "\0" + atom.AstPath);
        var occurrence = Convert.ToHexStringLower(SHA256.HashData(occurrenceBytes));
        var qualified = stem + "-" + occurrence;
        suggestedAtomIds.Add(qualified);
        return qualified;
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

    private static void MarkRejected(
        IEnumerable<DigestionLedgerEntry> entries,
        ImmutableDictionary<string, DigestionReceiptAlignment>.Builder alignments)
    {
        foreach (var entry in entries)
        {
            alignments[entry.AtomId] = DigestionReceiptAlignment.Rejected;
        }
    }

    private static string? AtomizerIntegrityFailure(
        AtomizedTheoryDocument document,
        ReadOnlySpan<byte> sourceBytes)
    {
        var sourceLength = sourceBytes.Length;
        if (document.Slices.Count(static slice => slice.IsClaim) != document.Claims.Length)
        {
            return "claim slice count does not match claim count";
        }

        if (!document.Reassemble().AsSpan().SequenceEqual(sourceBytes))
        {
            return "slices do not reassemble the source bytes";
        }

        var claimIndex = 0;
        var cursor = 0;
        foreach (var slice in document.Slices)
        {
            var end = cursor + slice.RawBytes.Length;
            if (slice.IsClaim)
            {
                var atom = document.Claims[claimIndex++];
                if (atom.StartByte != cursor || atom.EndByte != end)
                {
                    return $"claim {atom.AstPath} boundaries do not match its source slice";
                }

                if (!atom.RawBytes.AsSpan().SequenceEqual(slice.RawBytes.AsSpan()))
                {
                    return $"claim {atom.AstPath} raw bytes do not match its source span";
                }
            }

            cursor = end;
        }

        foreach (var atom in document.Claims)
        {
            if (string.IsNullOrWhiteSpace(atom.AstPath))
            {
                return "claim ast_path is empty";
            }

            if (atom.RawBytes.Length == 0
                || atom.StartByte < 0
                || atom.EndByte <= atom.StartByte
                || atom.EndByte > sourceLength
                || atom.EndByte - atom.StartByte != atom.RawBytes.Length)
            {
                return $"claim {atom.AstPath} has invalid byte boundaries";
            }

            if (atom.Fingerprints != DigestionFingerprint.Compute(atom.RawBytes.AsSpan()))
            {
                return $"claim {atom.AstPath} fingerprint does not match its raw bytes";
            }
        }

        return null;
    }

    private static bool EntryIdentityEqual(
        DigestionLedgerEntry candidate,
        DigestionLedgerEntry baseline) =>
        candidate.SourceId == baseline.SourceId
        && candidate.AtomId == baseline.AtomId
        && candidate.Fingerprints == baseline.Fingerprints;
}
