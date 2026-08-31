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
    Stale,
    Rejected,
}

internal static class DigestionReceiptAlignmentNames
{
    internal static string Render(DigestionReceiptAlignment value) => value switch
    {
        DigestionReceiptAlignment.Seen => "seen",
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

internal sealed record DigestionSourceClausePlan(
    string SourceId,
    DigestionAtom Parent,
    DigestionClausePlan Plan);

internal sealed record DigestionIngestFallback(string SourceId, string Reason);

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
    ImmutableArray<string> ActualStale,
    ImmutableArray<string> Findings)
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
        BackfillInventoryDocument? baselineDocument,
        DigestionAlignmentMode mode,
        Func<string, TheoryAtomizer>? atomizerResolver = null,
        RepositorySnapshot? baselineSnapshot = null,
        DigestionCasEvaluation? casEvaluation = null,
        RawChangeSet? changes = null,
        RawChangeSet? casChanges = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
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
        var verifiedClausePlanMembers = new HashSet<string>(StringComparer.Ordinal);
        var fallbacks = ImmutableArray.CreateBuilder<DigestionIngestFallback>();
        var suggestedAtomIds = sources
            .SelectMany(static source => source.Entries)
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var candidateEntriesById = sources
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
        var inheritedEntries = InheritedEntries(baselineDocument);
        foreach (var (source, entry) in sources.SelectMany(source =>
                     source.Entries.Select(entry => (Source: source, Entry: entry))))
        {
            var inherited = inheritedEntries.Contains(CanonicalEntry(source, entry));
            alignments[entry.AtomId] = cas.ValidAtomIds.Contains(entry.AtomId) && inherited
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

        var baselineSources = BaselineSources(baselineDocument, findings);
        var candidateSources = sources.ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        var contentWideReplacementObligationsBySource =
            new Dictionary<string, DigestionLedgerEntry[]>(StringComparer.Ordinal);
        var rejectedContentWideClones = new HashSet<string>(StringComparer.Ordinal);
        foreach (var baselineSource in baselineSources.Values)
        {
            candidateSources.TryGetValue(baselineSource.SourceId, out var candidateSource);
            var obligations = ContentWideReplacementObligations(
                baselineSource,
                candidateSource,
                snapshot);
            if (obligations.Length == 0)
            {
                continue;
            }

            contentWideReplacementObligationsBySource.Add(baselineSource.SourceId, obligations);
            if (candidateSource is null)
            {
                findings.Add(
                    "content-wide replacement source changed or disappeared: "
                    + baselineSource.SourceId);
            }
            else if (baselineSource.AcknowledgedStale.Any(id =>
                         obligations.Any(entry => entry.AtomId == id))
                     && !AtomizerRegistry.IsRegistered(candidateSource.Atomizer))
            {
                findings.Add(
                    "settled content-wide replacement requires a registered atomizer: "
                    + baselineSource.SourceId);
            }

            foreach (var baselineEntry in obligations)
            {
                foreach (var (candidateSourceId, candidateEntry) in sources.SelectMany(source =>
                             source.Entries.Select(entry => (source.SourceId, Entry: entry))))
                {
                    if (candidateEntry.AtomId == baselineEntry.AtomId
                        || candidateEntry.Fingerprints != baselineEntry.Fingerprints
                        || candidateEntry.CasRef != baselineEntry.CasRef
                        || candidateSourceId == baselineSource.SourceId
                            && ContentWideIdentityEqual(candidateEntry, baselineEntry))
                    {
                        continue;
                    }

                    if (rejectedContentWideClones.Add(candidateEntry.AtomId))
                    {
                        findings.Add(
                            $"source {baselineSource.SourceId} new content-wide receipt after "
                            + $"atomizer replacement: {candidateEntry.AtomId}");
                    }
                }
            }
        }

        var actualStale = new HashSet<string>(StringComparer.Ordinal);
        var knownContent = sources
            .SelectMany(static source => source.Entries)
            .Where(entry => cas.ValidAtomIds.Contains(entry.AtomId))
            .Select(static entry => entry.Fingerprints.RawSha256)
            .ToHashSet(StringComparer.Ordinal);

        foreach (var source in sources)
        {
            if (conflictedSources.Contains(source.SourceId))
            {
                continue;
            }

            var registeredAtomizer = AtomizerRegistry.IsRegistered(source.Atomizer);
            baselineSources.TryGetValue(source.SourceId, out var baselineSource);
            var contentWideReplacementObligations =
                contentWideReplacementObligationsBySource.GetValueOrDefault(source.SourceId) ?? [];
            var admissionGenreFinding = AdmissionGenreFinding(
                mode,
                snapshot,
                baselineSnapshot,
                source,
                baselineSource,
                registeredAtomizer,
                atomizerRules,
                atomizerResolver);
            if (admissionGenreFinding is not null)
            {
                findings.Add(admissionGenreFinding);
            }

            if (mode == DigestionAlignmentMode.Admission
                && !source.Entries.IsEmpty
                && source.Entries.All(entry =>
                    cas.ValidAtomIds.Contains(entry.AtomId)
                    && inheritedEntries.Contains(CanonicalEntry(source, entry)))
                && contentWideReplacementObligations.Length == 0
                && !InheritedClauseChainRequiresReplay(
                    source,
                    candidateSources,
                    candidateEntriesById,
                    inheritedEntries,
                    changes))
            {
                continue;
            }

            if (!registeredAtomizer)
            {
                genreRegistryChecks[source.SourceId] = GenreRegistryCheck.NoGenreRegistry;
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
            try
            {
                atomized = atomizerResolver(source.Atomizer)(sourceFile.RawBytes.AsSpan(), atomizerRules);
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

            var sourceStale = new List<string>();
            foreach (var baselineEntry in contentWideReplacementObligations.Where(entry =>
                         !producedAtomIds[source.SourceId].Contains(entry.AtomId)))
            {
                var exact = source.Entries
                    .Where(entry => ContentWideIdentityEqual(entry, baselineEntry))
                    .ToArray();
                if (exact.Length != 1)
                {
                    findings.Add(
                        $"source {source.SourceId} content-wide replacement receipt identity "
                        + $"changed or disappeared: {baselineEntry.AtomId}");
                    continue;
                }

                var entry = exact[0];
                if (!cas.ValidAtomIds.Contains(entry.AtomId))
                {
                    continue;
                }

                alignments[entry.AtomId] = DigestionReceiptAlignment.Stale;
                sourceStale.Add(entry.AtomId);
                actualStale.Add(entry.AtomId);
            }

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
                var matchingEntries = source.Entries.Where(entry =>
                        cas.ValidAtomIds.Contains(entry.AtomId)
                        && FingerprintsMatch(entry.Fingerprints, atom.Fingerprints))
                    .ToArray();
                foreach (var entry in matchingEntries)
                {
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
                atomized.ClausePlans,
                cas.ValidAtomIds,
                candidateEntriesById,
                snapshot,
                alignments,
                matchedAtoms,
                clausePlanChainParents,
                verifiedClausePlanParents,
                verifiedClausePlanMembers,
                findings);

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
            actualStale.Order(StringComparer.Ordinal).ToImmutableArray(),
            findings.Order(StringComparer.Ordinal).ToImmutableArray());
    }

    private static bool InheritedClauseChainRequiresReplay(
        DigestionLedgerSource source,
        IReadOnlyDictionary<string, DigestionLedgerSource> candidateSourcesById,
        IReadOnlyDictionary<string, DigestionLedgerEntry> candidateEntriesById,
        IReadOnlySet<string> inheritedEntries,
        RawChangeSet? changes)
    {
        if (!source.Entries.Any(static entry => !entry.Receipts.ChainAtoms.IsEmpty))
        {
            return false;
        }

        var relevantEntries = source.Entries.ToList();
        var relevantAtomIds = source.Entries
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var childId in source.Entries.SelectMany(static entry => entry.Receipts.ChainAtoms))
        {
            if (!candidateEntriesById.TryGetValue(childId, out var child))
            {
                return true;
            }

            if (!candidateSourcesById.TryGetValue(child.SourceId, out var childSource)
                || !inheritedEntries.Contains(CanonicalEntry(childSource, child)))
            {
                return true;
            }

            if (relevantAtomIds.Add(childId))
            {
                relevantEntries.Add(child);
            }
        }

        if (changes is null)
        {
            return false;
        }

        if (relevantEntries.Any(entry => DigestionCasStore.EntryChanged(entry, changes)))
        {
            return true;
        }

        var casPaths = relevantEntries
            .Select(static entry => DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..])
            .ToHashSet(StringComparer.Ordinal);
        return changes.Paths.Any(path =>
            path.Value == source.SourcePath
            || path.Value == TheoryAtomizerDataLoader.DataPath
            || IsAtomizerImplementationPath(path.Value)
            || casPaths.Contains(path.Value));
    }
}
