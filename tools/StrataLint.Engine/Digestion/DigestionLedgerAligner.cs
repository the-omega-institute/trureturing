using System.Collections.Immutable;
using System.Security.Cryptography;
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
    LegacyBoundary,
    Seen,
    Stale,
    Rejected,
}

internal static class DigestionReceiptAlignmentNames
{
    internal static string Render(DigestionReceiptAlignment value) => value switch
    {
        DigestionReceiptAlignment.LegacyBoundary => "legacy-boundary",
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

internal sealed record GenreResolutionReclassification(
    string SourceId,
    string AtomId,
    string AstPath);

internal sealed record DigestionLedgerAlignment(
    ImmutableDictionary<string, DigestionReceiptAlignment> EntryAlignments,
    ImmutableDictionary<string, DigestionAtom> MatchedAtoms,
    ImmutableDictionary<string, GenreRegistryCheck> GenreRegistryChecks,
    ImmutableArray<StructuredResidualAdmission> Residual,
    ImmutableArray<GenreResolutionReclassification> GenreReclassifications,
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
        DigestionCasEvaluation? casEvaluation = null)
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

        // Ingest is an explicit operation on the current tree, so a missing data file there is a
        // real fault. Admission judges arbitrary trees, including the baseline tree that predates
        // this data surface entirely; rejecting that tree would break conservative extension, so
        // the re-atomization below is skipped for it instead. A data file that IS present parses
        // fail-closed either way.
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
        var genreRegistryChecks = ImmutableDictionary.CreateBuilder<string, GenreRegistryCheck>(
            StringComparer.Ordinal);
        var residual = ImmutableArray.CreateBuilder<StructuredResidualAdmission>();
        var genreReclassifications = ImmutableArray.CreateBuilder<GenreResolutionReclassification>();
        var clausePlans = ImmutableArray.CreateBuilder<DigestionSourceClausePlan>();
        var clausePlanChainParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var verifiedClausePlanParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var fallbacks = ImmutableArray.CreateBuilder<DigestionIngestFallback>();
        var actualStale = ImmutableArray.CreateBuilder<string>();
        var suggestedAtomIds = new HashSet<string>(StringComparer.Ordinal);
        var cas = casEvaluation ?? DigestionCasStore.Evaluate(document, snapshot);
        findings.AddRange(cas.Findings);
        var inheritedEntries = InheritedEntries(baselineDocument);
        foreach (var entry in document.RequireDigestionEntries()
                     .Where(entry => cas.ValidAtomIds.Contains(entry.AtomId)
                         && inheritedEntries.Contains(CanonicalEntry(entry))))
        {
            var path = DigestionCasStore.RootPath + entry.CasRef["sha256:".Length..];
            if (snapshot.TryGetFile(path, out var blob))
            {
                matchedAtoms[entry.AtomId] = DigestionAtom.FromFrozenCas(entry.AstPath, blob.RawBytes);
            }
        }

        var baselineSources = BaselineSources(baselineDocument, findings);
        var candidateSources = sources.ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        var coarseReplacementObligationsBySource =
            new Dictionary<string, DigestionLedgerEntry[]>(StringComparer.Ordinal);
        var rejectedCoarseClones = new HashSet<string>(StringComparer.Ordinal);
        foreach (var baselineSource in baselineSources.Values)
        {
            candidateSources.TryGetValue(baselineSource.SourceId, out var candidateSource);
            var obligations = CoarseReplacementObligations(baselineSource, candidateSource);
            if (obligations.Length == 0)
            {
                continue;
            }

            coarseReplacementObligationsBySource.Add(baselineSource.SourceId, obligations);
            if (candidateSource is null)
            {
                findings.Add(
                    "coarse replacement source changed or disappeared: "
                    + baselineSource.SourceId);
            }

            foreach (var baselineEntry in obligations)
            {
                foreach (var (candidateSourceId, candidateEntry) in sources.SelectMany(source =>
                             source.Entries.Select(entry => (source.SourceId, Entry: entry))))
                {
                    if (candidateEntry.CasRef != baselineEntry.CasRef
                        || (candidateSourceId == baselineSource.SourceId
                            && CoarseReplacementIdentityEqual(candidateEntry, baselineEntry)))
                    {
                        continue;
                    }

                    if (rejectedCoarseClones.Add(candidateEntry.AtomId))
                    {
                        findings.Add(
                            $"source {baselineSource.SourceId} new coarse receipt after fine atomization: "
                            + candidateEntry.AtomId);
                    }
                }
            }
        }

        // One source at a time. Every early exit below is a decision about *this*
        // source only, which is why they read as returns: the pass either finishes
        // aligning the source or declines it, and the caller moves on to the next.
        void AlignSource(DigestionLedgerSource source)
        {
                baselineSources.TryGetValue(source.SourceId, out var baselineSource);
                var baselineHasFineEntries = baselineSource?.Entries.Any(static entry =>
                    entry.AstPath != "coarse/source") == true;
                foreach (var entry in source.Entries)
                {
                    alignments[entry.AtomId] = rejectedCoarseClones.Contains(entry.AtomId)
                        ? DigestionReceiptAlignment.Rejected
                        : source.Atomizer == AtomizerRegistry.NoAtomizerId
                            && entry.Boundary is not null
                                ? DigestionReceiptAlignment.LegacyBoundary
                                : cas.ValidAtomIds.Contains(entry.AtomId)
                                    && inheritedEntries.Contains(CanonicalEntry(entry))
                                    ? DigestionReceiptAlignment.Seen
                                    : DigestionReceiptAlignment.Rejected;
                }

                if (conflictedSources.Contains(source.SourceId))
                {
                    return;
                }

                var registeredAtomizer = AtomizerRegistry.IsRegistered(source.Atomizer);
                if (source.Atomizer == AtomizerRegistry.NoAtomizerId)
                {
                    genreRegistryChecks[source.SourceId] = GenreRegistryCheck.NoGenreRegistry;
                }
                var hasClausePlanChains = registeredAtomizer
                    && AtomizerRegistry.EmitsClausePlans(source.Atomizer)
                    && source.Entries.Any(static entry => entry.Receipts.ChainAtoms.Length > 0);
                var coarseReplacementObligations =
                    coarseReplacementObligationsBySource.GetValueOrDefault(source.SourceId, []);
                var unprovenCasEntries = source.Entries.Where(entry =>
                    cas.ValidAtomIds.Contains(entry.AtomId)
                    && !inheritedEntries.Contains(CanonicalEntry(entry))).ToArray();
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

                if (((mode == DigestionAlignmentMode.Admission
                        && unprovenCasEntries.Length == 0
                        && !hasClausePlanChains)
                        || !registeredAtomizer)
                    && coarseReplacementObligations.Length == 0)
                {
                    return;
                }

                if (!registeredAtomizer)
                {
                    if (coarseReplacementObligations.Any(entry =>
                            baselineSource?.AcknowledgedStale.Contains(
                                entry.AtomId,
                                StringComparer.Ordinal) == true))
                    {
                        findings.Add(
                            "settled coarse replacement requires a registered atomizer: "
                            + source.SourceId);
                    }

                    findings.Add(
                        $"source {source.SourceId} boundaryless receipts require a registered atomizer");
                    return;
                }

                if (!snapshot.TryGetFile(source.SourcePath, out var sourceFile))
                {
                    findings.Add($"source path is dangling: {source.SourcePath}");
                    return;
                }

                var opaqueFingerprints = DigestionFingerprint.ComputeOpaque(sourceFile.RawBytes.AsSpan());
                foreach (var entry in unprovenCasEntries.Where(static entry =>
                             entry.AstPath == "coarse/source"))
                {
                    if (rejectedCoarseClones.Contains(entry.AtomId)
                        || entry.Fingerprints != opaqueFingerprints)
                    {
                        continue;
                    }

                    matchedAtoms[entry.AtomId] = new DigestionAtom(
                        entry.AstPath,
                        0,
                        sourceFile.RawBytes.Length,
                        sourceFile.RawBytes,
                        opaqueFingerprints,
                        []);
                    alignments[entry.AtomId] = DigestionReceiptAlignment.Seen;
                }

                if (mode == DigestionAlignmentMode.Admission
                    && coarseReplacementObligations.Length == 0
                    && unprovenCasEntries.All(entry => matchedAtoms.ContainsKey(entry.AtomId))
                    && !hasClausePlanChains)
                {
                    return;
                }

                if (atomizerRules is null)
                {
                    // Tree predates the atomizer data surface: it cannot be re-atomized here, and
                    // reporting that as a finding would reject a tree the baseline harness admits.
                    return;
                }

                AtomizedTheoryDocument atomized;
                try
                {
                    var atomize = atomizerResolver(source.Atomizer);
                    atomized = atomize(sourceFile.RawBytes.AsSpan(), atomizerRules);
                }
                catch (Exception exception) when (
                    exception is TheorySourceFormatException or DecoderFallbackException)
                {
                    if (mode == DigestionAlignmentMode.Ingest)
                    {
                        if (baselineHasFineEntries)
                        {
                            // Plan throws on any finding, so one refusal fails repository-wide ingest.
                            // No verb covers total format retirement: acknowledged_stale is coarse-to-fine,
                            // while ActualStale covers partial fine regression. This is deliberately fail-closed.
                            findings.Add(
                                $"source {source.SourceId} cannot add coarse fallback after baseline "
                                + $"fine atomization: {exception.Message}");
                        }
                        else
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

                        return;
                    }

                    findings.Add($"source {source.SourceId} atomization failed: {exception.Message}");
                    return;
                }

                var integrityFailure = AtomizerIntegrityFailure(
                    atomized,
                    sourceFile.RawBytes.AsSpan());
                if (integrityFailure is not null)
                {
                    findings.Add(
                        $"source {source.SourceId} atomizer integrity failed: {integrityFailure}");
                    return;
                }

                genreRegistryChecks[source.SourceId] = atomized.GenreRegistryCheck;

                if (atomized.Claims.Length == 0)
                {
                    if (mode == DigestionAlignmentMode.Ingest)
                    {
                        const string reason = "atomizer recognition is incomplete or empty";
                        if (baselineHasFineEntries)
                        {
                            // Plan throws on any finding, so one refusal fails repository-wide ingest.
                            // No verb covers total format retirement: acknowledged_stale is coarse-to-fine,
                            // while ActualStale covers partial fine regression. This is deliberately fail-closed.
                            findings.Add(
                                $"source {source.SourceId} cannot add coarse fallback after baseline "
                                + $"fine atomization: {reason}");
                        }
                        else
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

                        return;
                    }

                    findings.Add($"source {source.SourceId} atomizer recognition is incomplete or empty");
                    return;
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
                    return;
                }

                foreach (var plan in atomized.ClausePlans)
                {
                    var parent = claims[plan.ParentAstPath];
                    var authorityFailure = ClausePlanCasAuthorityFailure(
                        source,
                        parent,
                        cas.ValidAtomIds,
                        snapshot);
                    if (authorityFailure is not null)
                    {
                        findings.Add(authorityFailure);
                        continue;
                    }

                    clausePlans.Add(new DigestionSourceClausePlan(source.SourceId, parent, plan));
                }

                var matchedAstPaths = new HashSet<string>(StringComparer.Ordinal);
                var reclassifiedAtomIds = new HashSet<string>(StringComparer.Ordinal);
                if (mode == DigestionAlignmentMode.Ingest && atomizerRules is not null)
                {
                    foreach (var atom in atomized.Claims)
                    {
                        var candidates = source.Entries.Where(entry =>
                                cas.ValidAtomIds.Contains(entry.AtomId)
                                && entry.Fingerprints.RawSha256 == atom.Fingerprints.RawSha256
                                && UnregisteredGenreLocator.TryGetToken(entry.AstPath, out var token)
                                && source.GenreRegistryCheck.Kind == GenreRegistryCheckKind.Collected
                                && source.GenreRegistryCheck.UnregisteredGenres.Contains(
                                    token,
                                    StringComparer.Ordinal)
                                && IsExactGenreResolution(
                                    source.Atomizer,
                                    token,
                                    entry.AstPath,
                                    atom.AstPath,
                                    atomizerRules))
                            .ToArray();
                        if (candidates.Length == 0)
                        {
                            continue;
                        }

                        if (candidates.Length != 1
                            || !reclassifiedAtomIds.Add(candidates[0].AtomId))
                        {
                            findings.Add(
                                $"source {source.SourceId} genre reclassification is ambiguous: "
                                + atom.AstPath);
                            continue;
                        }

                        var existing = candidates[0];
                        if (source.Entries.Any(entry =>
                                entry.AtomId != existing.AtomId
                                && entry.AstPath == atom.AstPath))
                        {
                            findings.Add(
                                $"source {source.SourceId} genre reclassification ast_path collides: "
                                + atom.AstPath);
                            continue;
                        }

                        matchedAstPaths.Add(atom.AstPath);
                        matchedAtoms[existing.AtomId] = atom;
                        alignments[existing.AtomId] = DigestionReceiptAlignment.Seen;
                        genreReclassifications.Add(new GenreResolutionReclassification(
                            source.SourceId,
                            existing.AtomId,
                            atom.AstPath));
                    }
                }

                var sourceStale = new List<string>();
                if (coarseReplacementObligations.Length > 0 && !claims.ContainsKey("coarse/source"))
                {
                    foreach (var baselineEntry in coarseReplacementObligations)
                    {
                        var exact = source.Entries
                            .Where(entry => CoarseReplacementIdentityEqual(entry, baselineEntry))
                            .ToArray();
                        if (exact.Length != 1)
                        {
                            findings.Add(
                                $"source {source.SourceId} coarse replacement receipt identity changed "
                                + $"or disappeared: {baselineEntry.AtomId}");
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
                }

                foreach (var legacy in source.Entries.Where(static entry => entry.Boundary is not null))
                {
                    if (claims.TryGetValue(legacy.AstPath, out var atom)
                        && FingerprintsMatch(atom.Fingerprints, legacy.Fingerprints))
                    {
                        matchedAstPaths.Add(atom.AstPath);
                        matchedAtoms[legacy.AtomId] = atom;
                    }
                }

                foreach (var entry in source.Entries.Where(entry =>
                             cas.ValidAtomIds.Contains(entry.AtomId)))
                {
                    if (claims.TryGetValue(entry.AstPath, out var atom)
                        && FingerprintsMatch(atom.Fingerprints, entry.Fingerprints))
                    {
                        matchedAstPaths.Add(atom.AstPath);
                        matchedAtoms[entry.AtomId] = atom;
                        alignments[entry.AtomId] = DigestionReceiptAlignment.Seen;
                    }
                }


                AlignNestedChildren(
                    source,
                    atomized.ClausePlans,
                    claims,
                    cas.ValidAtomIds,
                    snapshot,
                    alignments,
                    matchedAtoms,
                    clausePlanChainParents,
                    verifiedClausePlanParents,
                    findings);

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

        foreach (var source in sources)
        {
            AlignSource(source);
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
            genreRegistryChecks.ToImmutable(),
            residual.ToImmutable(),
            genreReclassifications.ToImmutable(),
            clausePlans.ToImmutable(),
            clausePlanChainParents.ToImmutable(),
            verifiedClausePlanParents.ToImmutable(),
            fallbacks.ToImmutable(),
            actualStale.Order(StringComparer.Ordinal).ToImmutableArray(),
            findings.Order(StringComparer.Ordinal).ToImmutableArray());
    }

}
