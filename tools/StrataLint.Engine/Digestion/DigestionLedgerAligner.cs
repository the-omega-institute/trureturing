using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal enum DigestionAlignmentMode
{
    Admission,
    Ingest,
    Projection,
}

internal enum DigestionReceiptAlignment
{
    Seen,
    Rejected,
}

internal static class DigestionReceiptAlignmentNames
{
    internal static string Render(DigestionReceiptAlignment value) => value switch
    {
        DigestionReceiptAlignment.Seen => "seen",
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

internal sealed record DigestionSourceClausePlan(
    string SourceId,
    DigestionAtom Parent,
    DigestionClausePlan Plan);

internal sealed record DigestionIngestFallback(string SourceId, string Reason);

internal sealed record DigestionContentKindObservation(
    string SourceId,
    string AtomId,
    string? ContentKind);

internal sealed record DigestionLedgerAlignment(
    ImmutableDictionary<string, DigestionReceiptAlignment> EntryAlignments,
    ImmutableDictionary<string, DigestionAtom> MatchedAtoms,
    ImmutableDictionary<string, ImmutableHashSet<string>> ProducedAtomIds,
    ImmutableDictionary<string, GenreRegistryCheck> GenreRegistryChecks,
    ImmutableArray<StructuredResidualAdmission> Residual,
    ImmutableArray<DigestionSourceClausePlan> ClausePlans,
    ImmutableHashSet<string> ClausePlanChainParents,
    ImmutableHashSet<string> VerifiedClausePlanParents,
    ImmutableArray<DigestionIngestFallback> Fallbacks,
    ImmutableArray<string> Findings,
    ImmutableArray<DigestionContentKindObservation> ContentKindObservations = default)
{
    internal DigestionReceiptAlignment AlignmentFor(string atomId) =>
        EntryAlignments.TryGetValue(atomId, out var alignment)
            ? alignment
            : throw new InvalidOperationException($"digestion alignment omitted entry {atomId}");

    internal DigestionAtom? AtomFor(string atomId) => MatchedAtoms.GetValueOrDefault(atomId);

    internal bool IsProduced(string sourceId, string atomId) =>
        ProducedAtomIds.TryGetValue(sourceId, out var ids) && ids.Contains(atomId);
}

internal static partial class DigestionLedgerAligner
{
    internal static DigestionLedgerAlignment Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        DigestionAlignmentMode mode,
        Func<string, TheoryAtomizer>? atomizerResolver = null,
        DigestionCasEvaluation? casEvaluation = null,
        RawChangeSet? changes = null,
        RawChangeSet? casChanges = null,
        Func<string, TheoryAtomizerWithContentKinds>? contentKindAtomizerResolver = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        if (atomizerResolver is null && contentKindAtomizerResolver is null)
        {
            contentKindAtomizerResolver = static id =>
                AtomizerRegistry.Require(id).AtomizeWithContentKinds;
        }
        atomizerResolver ??= static id => AtomizerRegistry.Require(id).Atomize;

        var findings = ImmutableArray.CreateBuilder<string>();
        var sources = document.RequireDigestionSources();
        var conflictedSources = new HashSet<string>(StringComparer.Ordinal);
        foreach (var source in sources)
        {
            if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile)
                || DigestionSourceConflictMarkers.FindFirstLine(sourceFile.RawBytes.AsSpan()) is not { } line)
            {
                continue;
            }

            var finding = DigestionSourceConflictMarkers.FormatFinding(source.SourcePath, line);
            if (mode == DigestionAlignmentMode.Ingest)
            {
                throw new FormatException(finding);
            }

            findings.Add(finding);
            conflictedSources.Add(source.SourceId);
        }

        TheoryAtomizerRules? atomizerRules;
        if (!TheoryAtomizerDataLoader.TryLoad(snapshot, out var loadedRules))
        {
            if (mode == DigestionAlignmentMode.Ingest)
            {
                throw new FormatException(
                    $"Atomizer data file is missing: {TheoryAtomizerDataLoader.DataPath}");
            }

            atomizerRules = null;
        }
        else
        {
            atomizerRules = loadedRules;
        }

        var alignments = ImmutableDictionary.CreateBuilder<string, DigestionReceiptAlignment>(
            StringComparer.Ordinal);
        var matchedAtoms = ImmutableDictionary.CreateBuilder<string, DigestionAtom>(StringComparer.Ordinal);
        var producedAtomIds = ImmutableDictionary.CreateBuilder<string, ImmutableHashSet<string>>(
            StringComparer.Ordinal);
        var genreRegistryChecks = ImmutableDictionary.CreateBuilder<string, GenreRegistryCheck>(
            StringComparer.Ordinal);
        var residual = ImmutableArray.CreateBuilder<StructuredResidualAdmission>();
        var clausePlans = ImmutableArray.CreateBuilder<DigestionSourceClausePlan>();
        var clausePlanChainParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var verifiedClausePlanParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var contentKindObservations = ImmutableArray.CreateBuilder<DigestionContentKindObservation>();
        var fallbacks = ImmutableArray.CreateBuilder<DigestionIngestFallback>();
        var suggestedAtomIds = sources
            .SelectMany(static source => source.Entries)
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var globalEntriesById = sources
            .SelectMany(static source => source.Entries)
            .GroupBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .Where(static group => group.Count() == 1)
            .ToDictionary(static group => group.Key, static group => group.Single(), StringComparer.Ordinal);

        casChanges ??= changes;
        if (casEvaluation is not null && !casEvaluation.Matches(casChanges))
        {
            throw new ArgumentException(
                "CAS evaluation scope does not match the alignment change set.",
                nameof(casEvaluation));
        }

        var cas = casEvaluation ?? DigestionCasStore.Evaluate(document, snapshot, casChanges);
        findings.AddRange(cas.Findings);
        foreach (var (source, entry) in sources
                     .SelectMany(source =>
                     source.Entries.Select(entry => (Source: source, Entry: entry))))
        {
            // An entry is seen when its content-addressed atom is intact. Whether the
            // source document still contains that text does not decide it.
            alignments[entry.AtomId] = cas.ValidAtomIds.Contains(entry.AtomId)
                ? DigestionReceiptAlignment.Seen
                : DigestionReceiptAlignment.Rejected;
            if (!cas.ValidAtomIds.Contains(entry.AtomId))
            {
                continue;
            }

            var path = DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..];
            if (snapshot.TryGetFile(path, out var blob))
            {
                matchedAtoms[entry.AtomId] = DigestionAtom.FromFrozenCas(
                    blob.RawBytes,
                    entry.Fingerprints);
            }
        }

        var knownContent = sources
            .SelectMany(static source => source.Entries)
            .Where(entry => cas.ValidAtomIds.Contains(entry.AtomId))
            .Select(static entry => entry.Fingerprints.RawSha256)
            .ToHashSet(StringComparer.Ordinal);

        var atomizerInputsChanged = new Lazy<bool>(() =>
            changes is not null && AtomizerInputsChanged(changes, snapshot));
        foreach (var source in sources)
        {
            if (conflictedSources.Contains(source.SourceId))
            {
                continue;
            }

            // A change set limits which sources are replayed. It never changes what
            // a replayed source yields.
            if (mode == DigestionAlignmentMode.Admission
                && changes is not null
                && !source.Entries.IsEmpty
                && source.Entries.All(entry => cas.ValidAtomIds.Contains(entry.AtomId))
                && !SourceChanged(source, changes)
                && !atomizerInputsChanged.Value)
            {
                continue;
            }

            var registeredAtomizer = AtomizerRegistry.IsRegistered(source.Atomizer);
            var validateGenreProjection = mode == DigestionAlignmentMode.Admission;
            if (!registeredAtomizer)
            {
                genreRegistryChecks[source.SourceId] = GenreRegistryCheck.NoGenreRegistry;
                if (validateGenreProjection
                    && source.Atomizer == AtomizerRegistry.NoAtomizerId
                    && !GenreRegistryChecksEqual(
                        source.GenreRegistryCheck,
                        GenreRegistryCheck.NoGenreRegistry))
                {
                    findings.Add(GenreRegistryProjectionFinding(
                        source,
                        source.GenreRegistryCheck,
                        GenreRegistryCheck.NoGenreRegistry));
                }
                continue;
            }

            if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
            {
                findings.Add($"source path is dangling: {source.SourcePath}");
                continue;
            }

            if (atomizerRules is null)
            {
                continue;
            }

            AtomizedTheoryDocument atomized;
            var atomizedContentKinds = new Dictionary<string, string>(StringComparer.Ordinal);
            try
            {
                atomized = contentKindAtomizerResolver is null
                    ? atomizerResolver(source.Atomizer)(sourceFile.RawBytes.AsSpan(), atomizerRules)
                    : contentKindAtomizerResolver(source.Atomizer)(
                        sourceFile.RawBytes.AsSpan(),
                        atomizerRules,
                        atomizedContentKinds);
            }
            catch (Exception exception) when (
                exception is TheorySourceFormatException or DecoderFallbackException)
            {
                var contentWideEntry = ContentWideEntry(
                    source,
                    sourceFile.RawBytes.AsSpan(),
                    cas.ValidAtomIds);
                if (contentWideEntry is not null)
                {
                    alignments[contentWideEntry.AtomId] = DigestionReceiptAlignment.Seen;
                    producedAtomIds[source.SourceId] = [contentWideEntry.AtomId];
                    if (mode == DigestionAlignmentMode.Ingest)
                    {
                        AddCoarseFallback(
                            source,
                            sourceFile.RawBytes,
                            exception.Message,
                            cas.ValidAtomIds,
                            suggestedAtomIds,
                            residual,
                            fallbacks);
                    }
                }
                else if (mode == DigestionAlignmentMode.Ingest && source.Entries.IsEmpty)
                {
                    AddCoarseFallback(
                        source,
                        sourceFile.RawBytes,
                        exception.Message,
                        cas.ValidAtomIds,
                        suggestedAtomIds,
                        residual,
                        fallbacks);
                }
                else
                {
                    findings.Add($"source {source.SourceId} atomization failed: {exception.Message}");
                }

                continue;
            }

            var integrityFailure = AtomizerIntegrityFailure(atomized, sourceFile.RawBytes.AsSpan());
            if (integrityFailure is not null)
            {
                findings.Add($"source {source.SourceId} atomizer integrity failed: {integrityFailure}");
                continue;
            }

            genreRegistryChecks[source.SourceId] = atomized.GenreRegistryCheck;
            if (validateGenreProjection
                && !GenreRegistryChecksEqual(
                    source.GenreRegistryCheck,
                    atomized.GenreRegistryCheck))
            {
                findings.Add(GenreRegistryProjectionFinding(
                    source,
                    source.GenreRegistryCheck,
                    atomized.GenreRegistryCheck));
            }

            if (atomized.Claims.IsEmpty)
            {
                const string reason = "atomizer recognition is incomplete or empty";
                var contentWideEntry = ContentWideEntry(
                    source,
                    sourceFile.RawBytes.AsSpan(),
                    cas.ValidAtomIds);
                if (contentWideEntry is not null)
                {
                    alignments[contentWideEntry.AtomId] = DigestionReceiptAlignment.Seen;
                    producedAtomIds[source.SourceId] = [contentWideEntry.AtomId];
                    if (mode == DigestionAlignmentMode.Ingest)
                    {
                        AddCoarseFallback(
                            source,
                            sourceFile.RawBytes,
                            reason,
                            cas.ValidAtomIds,
                            suggestedAtomIds,
                            residual,
                            fallbacks);
                    }
                }
                else if (mode == DigestionAlignmentMode.Ingest && source.Entries.IsEmpty)
                {
                    AddCoarseFallback(
                        source,
                        sourceFile.RawBytes,
                        reason,
                        cas.ValidAtomIds,
                        suggestedAtomIds,
                        residual,
                        fallbacks);
                }
                else
                {
                    findings.Add($"source {source.SourceId} {reason}");
                }

                continue;
            }

            var claims = atomized.Claims
                .GroupBy(static atom => atom.Fingerprints.RawSha256, StringComparer.Ordinal)
                .Select(static group => group.First())
                .ToArray();
            producedAtomIds[source.SourceId] = claims
                .Select(static atom => atom.Fingerprints.RawSha256["sha256:".Length..])
                .ToImmutableHashSet(StringComparer.Ordinal);

            foreach (var plan in atomized.ClausePlans
                         .GroupBy(static plan => plan.Parent.Fingerprints.RawSha256, StringComparer.Ordinal)
                         .Select(static group => group.First()))
            {
                var authorityFailure = ClausePlanCasAuthorityFailure(
                    source,
                    plan.Parent,
                    cas.ValidAtomIds,
                    snapshot);
                if (authorityFailure is not null)
                {
                    findings.Add(authorityFailure);
                    continue;
                }

                clausePlans.Add(new DigestionSourceClausePlan(source.SourceId, plan.Parent, plan));
            }

            foreach (var atom in claims)
            {
                atomizedContentKinds.TryGetValue(atom.Fingerprints.RawSha256, out var contentKind);
                var matchingEntries = source.Entries.Where(entry =>
                        cas.ValidAtomIds.Contains(entry.AtomId)
                        && FingerprintsMatch(entry.Fingerprints, atom.Fingerprints))
                    .ToArray();
                if (matchingEntries.Length == 0)
                {
                    contentKindObservations.Add(new DigestionContentKindObservation(
                        source.SourceId,
                        atom.Fingerprints.RawSha256["sha256:".Length..],
                        contentKind));
                }
                foreach (var entry in matchingEntries)
                {
                    contentKindObservations.Add(new DigestionContentKindObservation(
                        source.SourceId,
                        entry.AtomId,
                        contentKind));
                    matchedAtoms[entry.AtomId] = atom;
                    alignments[entry.AtomId] = DigestionReceiptAlignment.Seen;
                }

                if (knownContent.Contains(atom.Fingerprints.RawSha256))
                {
                    continue;
                }

                knownContent.Add(atom.Fingerprints.RawSha256);
                var atomId = SuggestedAtomId(
                    atom,
                    suggestedAtomIds);
                residual.Add(new StructuredResidualAdmission(
                    source.SourceId,
                    source.SourcePath,
                    source.Atomizer,
                    atom,
                    atomId,
                    new DigestionStatus(
                        DigestionMigrationState.Residual,
                        DigestionTruthState.Open)));
            }

            AlignNestedChildren(
                source,
                cas.ValidAtomIds,
                globalEntriesById,
                snapshot,
                alignments,
                matchedAtoms,
                clausePlanChainParents,
                verifiedClausePlanParents,
                findings);
        }

        return new DigestionLedgerAlignment(
            alignments.ToImmutable(),
            matchedAtoms.ToImmutable(),
            producedAtomIds.ToImmutable(),
            genreRegistryChecks.ToImmutable(),
            residual.ToImmutable(),
            clausePlans.ToImmutable(),
            clausePlanChainParents.ToImmutable(),
            verifiedClausePlanParents.ToImmutable(),
            fallbacks.ToImmutable(),
            findings.Order(StringComparer.Ordinal).ToImmutableArray(),
            contentKindObservations.ToImmutable());
    }

}
