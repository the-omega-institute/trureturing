using System.Collections.Immutable;

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

internal sealed record DigestionLedgerAlignment(
    ImmutableDictionary<string, DigestionReceiptAlignment> EntryAlignments,
    ImmutableArray<StructuredResidualAdmission> Residual,
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
        var residual = ImmutableArray.CreateBuilder<StructuredResidualAdmission>();
        var actualStale = ImmutableArray.CreateBuilder<string>();
        var findings = ImmutableArray.CreateBuilder<string>();
        var baselineSources = BaselineSources(baselineDocument, findings);
        foreach (var source in document.RequireDigestionSources())
        {
            foreach (var entry in source.Entries.Where(static entry => entry.Boundary is not null))
            {
                alignments[entry.AtomId] = DigestionReceiptAlignment.LegacyBoundary;
            }

            var structuredEntries = source.Entries
                .Where(static entry => entry.Boundary is null)
                .ToArray();
            if (structuredEntries.Length == 0)
            {
                continue;
            }

            if (!AtomizerRegistry.IsRegistered(source.Atomizer))
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
            catch (FormatException exception)
            {
                findings.Add($"source {source.SourceId} atomization failed: {exception.Message}");
                MarkRejected(structuredEntries, alignments);
                continue;
            }

            if (!RecognitionIsComplete(atomized, sourceFile.RawBytes.AsSpan()))
            {
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
                    matchedAstPaths.Add(atom.AstPath);
                    continue;
                }

                if (atom is not null
                    && atom.Fingerprints.NormalizedSha256 == entry.Fingerprints.NormalizedSha256)
                {
                    alignments[entry.AtomId] = DigestionReceiptAlignment.NormalizedSeen;
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

            var rawResidual = new HashSet<string>(StringComparer.Ordinal);
            var normalizedResidual = new HashSet<string>(StringComparer.Ordinal);
            var registration = AtomizerRegistry.Require(source.Atomizer);
            foreach (var atom in atomized.Claims.Where(atom => !matchedAstPaths.Contains(atom.AstPath)))
            {
                if (!rawResidual.Add(atom.Fingerprints.RawSha256))
                {
                    findings.Add(
                        $"source {source.SourceId} duplicate raw residual fingerprint: {atom.AstPath}");
                    continue;
                }

                if (!normalizedResidual.Add(atom.Fingerprints.NormalizedSha256))
                {
                    findings.Add(
                        $"source {source.SourceId} duplicate normalized residual fingerprint: {atom.AstPath}");
                    continue;
                }

                residual.Add(new StructuredResidualAdmission(
                    source.SourceId,
                    source.SourcePath,
                    source.Atomizer,
                    atom,
                    registration.ResidualPrefix
                    + "-residual-"
                    + atom.Fingerprints.RawSha256["sha256:".Length..],
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
            residual.ToImmutable(),
            actualStale.Order(StringComparer.Ordinal).ToImmutableArray(),
            findings.Order(StringComparer.Ordinal).ToImmutableArray());
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

    private static bool RecognitionIsComplete(
        AtomizedTheoryDocument document,
        ReadOnlySpan<byte> sourceBytes)
    {
        var sourceLength = sourceBytes.Length;
        if (document.Claims.Length == 0
            || document.Slices.Count(static slice => slice.IsClaim) != document.Claims.Length
            || !document.Reassemble().AsSpan().SequenceEqual(sourceBytes))
        {
            return false;
        }

        return document.Claims.All(atom =>
            !string.IsNullOrWhiteSpace(atom.AstPath)
            && atom.RawBytes.Length > 0
            && atom.StartByte >= 0
            && atom.EndByte > atom.StartByte
            && atom.EndByte <= sourceLength
            && atom.EndByte - atom.StartByte == atom.RawBytes.Length
            && atom.Fingerprints == DigestionFingerprint.Compute(atom.RawBytes.AsSpan()));
    }

    private static bool EntryIdentityEqual(
        DigestionLedgerEntry candidate,
        DigestionLedgerEntry baseline) =>
        candidate.SourceId == baseline.SourceId
        && candidate.AtomId == baseline.AtomId
        && candidate.Fingerprints == baseline.Fingerprints;
}
