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
    ImmutableDictionary<string, ImmutableHashSet<string>> ProducedAstPaths,
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

    internal bool IsProduced(string sourceId, string astPath) =>
        ProducedAstPaths.TryGetValue(sourceId, out var paths) && paths.Contains(astPath);
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
        var producedAstPaths = ImmutableDictionary.CreateBuilder<string, ImmutableHashSet<string>>(
            StringComparer.Ordinal);
        var genreRegistryChecks = ImmutableDictionary.CreateBuilder<string, GenreRegistryCheck>(
            StringComparer.Ordinal);
        var residual = ImmutableArray.CreateBuilder<StructuredResidualAdmission>();
        var genreReclassifications = ImmutableArray.CreateBuilder<GenreResolutionReclassification>();
        var clausePlans = ImmutableArray.CreateBuilder<DigestionSourceClausePlan>();
        var clausePlanChainParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var verifiedClausePlanParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var fallbacks = ImmutableArray.CreateBuilder<DigestionIngestFallback>();
        var actualStale = ImmutableArray.CreateBuilder<string>();
        // Existing IDs occupy the legacy content-stem namespace. Seed the suggestion set so
        // repeated residuals can receive deterministic source/locator qualification. An
        // existing stem can still be selected below when ingest must decide whether its
        // content-identical entry moved or remains a true collision.
        var suggestedAtomIds = sources
            .SelectMany(static source => source.Entries)
            .Select(static entry => entry.AtomId)
            .ToHashSet(StringComparer.Ordinal);
        var ownedAtomIds = FindOwnedAtomIds(
            snapshot,
            sources.SelectMany(static source => source.Entries)
                .Select(static entry => entry.AtomId));
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
                     source.Entries.Select(entry => (Source: source, Entry: entry)))
                     .Where(item => cas.ValidAtomIds.Contains(item.Entry.AtomId)
                         && inheritedEntries.Contains(CanonicalEntry(
                             item.Source,
                             item.Entry))))
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
                                    && inheritedEntries.Contains(CanonicalEntry(
                                        source,
                                        entry))
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
                var chainInputsChanged = hasClausePlanChains
                    && ClausePlanInputsChanged(source, changes);
                var coarseReplacementObligations =
                    coarseReplacementObligationsBySource.GetValueOrDefault(source.SourceId, []);
                var unprovenCasEntries = source.Entries.Where(entry =>
                    cas.ValidAtomIds.Contains(entry.AtomId)
                    && !inheritedEntries.Contains(CanonicalEntry(
                        source,
                        entry))).ToArray();
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
                        && !chainInputsChanged)
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
                    && !chainInputsChanged)
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

                producedAstPaths[source.SourceId] = claims.Keys.ToImmutableHashSet(StringComparer.Ordinal);

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
                string ResidualStem(DigestionAtom atom) => registration.ResidualPrefix
                    + "-residual-"
                    + atom.Fingerprints.RawSha256["sha256:".Length..];
                static string AstPathKind(string astPath)
                {
                    var separator = astPath.IndexOf('/', StringComparison.Ordinal);
                    return separator < 0 ? astPath : astPath[..separator];
                }
                var duplicateResidualStems = atomized.Claims
                    .GroupBy(
                        ResidualStem,
                        StringComparer.Ordinal)
                    .Where(static group => group.Count() > 1)
                    .Select(static group => group.Key)
                    .ToHashSet(StringComparer.Ordinal);
                foreach (var atom in atomized.Claims)
                {
                    var matchingAtomIds = source.Entries
                        .Where(entry => cas.ValidAtomIds.Contains(entry.AtomId)
                            && entry.AstPath == atom.AstPath
                            && FingerprintsMatch(entry.Fingerprints, atom.Fingerprints))
                        .Select(static entry => entry.AtomId)
                        .Distinct(StringComparer.Ordinal)
                        .ToArray();
                    string? authoritativeAtomId = matchingAtomIds.Length == 1
                        ? matchingAtomIds[0]
                        : null;
                    if (!matchedAstPaths.Contains(atom.AstPath))
                    {
                        var residualStem = ResidualStem(atom);
                        var existingStem = source.Entries.FirstOrDefault(entry =>
                            entry.AtomId == residualStem
                            && FingerprintsMatch(entry.Fingerprints, atom.Fingerprints));
                        var preserveExistingStem = existingStem is not null
                            && AstPathKind(existingStem.AstPath) == AstPathKind(atom.AstPath)
                            && (!claims.ContainsKey(existingStem.AstPath)
                                || source.Atomizer == AtomizerRegistry.GenericId);
                        authoritativeAtomId = preserveExistingStem
                            ? residualStem
                            : SuggestedAtomId(
                                source,
                                registration,
                                atom,
                                "residual",
                                suggestedAtomIds,
                                duplicateResidualStems);
                        residual.Add(new StructuredResidualAdmission(
                            source.SourceId,
                            source.SourcePath,
                            source.Atomizer,
                            atom,
                            authoritativeAtomId,
                            new DigestionStatus(
                                DigestionMigrationState.Residual,
                                DigestionTruthState.Open)));
                    }

                    if (authoritativeAtomId is null)
                    {
                        continue;
                    }

                    foreach (var priorGeneration in source.Entries.Where(entry =>
                                 entry.AstPath == atom.AstPath
                                 && entry.AtomId != authoritativeAtomId
                                 && !FingerprintsMatch(entry.Fingerprints, atom.Fingerprints)))
                    {
                        if (!CanAcknowledgeSupersededGeneration(
                            priorGeneration,
                            alignments.GetValueOrDefault(priorGeneration.AtomId),
                            ownedAtomIds))
                        {
                            continue;
                        }

                        actualStale.Add(priorGeneration.AtomId);
                        if (alignments.GetValueOrDefault(priorGeneration.AtomId)
                                != DigestionReceiptAlignment.Seen
                            || !IsUnownedResidualOpen(priorGeneration, ownedAtomIds))
                        {
                            continue;
                        }

                        alignments[priorGeneration.AtomId] = DigestionReceiptAlignment.Stale;
                        sourceStale.Add(priorGeneration.AtomId);
                    }
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

        // 「已入库、尚未消化」不再是阻断判词。它是账本四态里的 `open`:内容层、
        // 完全可逆、随时可由 producer(`make ingest`)重新检出,归 CLAUDE.md 第 20 条
        // 「允许犯错 + 事后检测 + 快速勘正」,不归事前硬门。
        //
        // 为何不做「只豁免本 PR 自己改的理论卷」:那种窄豁免会在合入后毒化 dev——
        // 同一批未闭合原子对**后续每个** PR 都不再豁免,全仓变红(仓内先例:
        // SL-003 曾锁死七个在飞 PR)。一律非阻断则谁也堵不住,不可能毒化。
        //
        // 残余本身已在 DigestionLedgerAlignment.Residual 上暴露,消费者据此发出
        // AdmissionEffect.Observe 的观察项,不经字符串匹配区分效力。

        return new DigestionLedgerAlignment(
            alignments.ToImmutable(),
            matchedAtoms.ToImmutable(),
            producedAstPaths.ToImmutable(),
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
