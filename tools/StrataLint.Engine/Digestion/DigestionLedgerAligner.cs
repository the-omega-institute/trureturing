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

internal sealed record DigestionLedgerAlignment(
    ImmutableDictionary<string, DigestionReceiptAlignment> EntryAlignments,
    ImmutableDictionary<string, DigestionAtom> MatchedAtoms,
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
}

internal static partial class DigestionLedgerAligner
{
    internal static DigestionLedgerAlignment Evaluate(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument? baselineDocument,
        DigestionAlignmentMode mode,
        Func<string, TheoryAtomizer>? atomizerResolver = null,
        RepositorySnapshot? baselineSnapshot = null)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(snapshot);
        atomizerResolver ??= static id => AtomizerRegistry.Require(id).Atomize;
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
        var residual = ImmutableArray.CreateBuilder<StructuredResidualAdmission>();
        var clausePlans = ImmutableArray.CreateBuilder<DigestionSourceClausePlan>();
        var clausePlanChainParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var verifiedClausePlanParents = ImmutableHashSet.CreateBuilder<string>(StringComparer.Ordinal);
        var fallbacks = ImmutableArray.CreateBuilder<DigestionIngestFallback>();
        var actualStale = ImmutableArray.CreateBuilder<string>();
        var findings = ImmutableArray.CreateBuilder<string>();
        var suggestedAtomIds = new HashSet<string>(StringComparer.Ordinal);
        var cas = DigestionCasStore.Evaluate(document, snapshot);
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
        var sources = document.RequireDigestionSources();
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

                var registeredAtomizer = AtomizerRegistry.IsRegistered(source.Atomizer);
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
                        AddCoarseFallback(
                            source,
                            sourceFile.RawBytes,
                            exception.Message,
                            cas.ValidAtomIds,
                            suggestedAtomIds,
                            residual,
                            fallbacks);
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

                // Ingest must refuse the addressed token instead of degrading the whole volume
                // to a coarse atom. Admission has a separate probe so reconciliation outcomes
                // remain unchanged.
                if (mode != DigestionAlignmentMode.Admission
                    && !atomized.UnregisteredGenres.IsEmpty)
                {
                    findings.Add(UnregisteredGenreFinding(source, atomized.UnregisteredGenres));
                    return;
                }

                if (atomized.Claims.Length == 0)
                {
                    if (mode == DigestionAlignmentMode.Ingest)
                    {
                        AddCoarseFallback(
                            source,
                            sourceFile.RawBytes,
                            "atomizer recognition is incomplete or empty",
                            cas.ValidAtomIds,
                            suggestedAtomIds,
                            residual,
                            fallbacks);
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
            residual.ToImmutable(),
            clausePlans.ToImmutable(),
            clausePlanChainParents.ToImmutable(),
            verifiedClausePlanParents.ToImmutable(),
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

    private static HashSet<string> InheritedEntries(
        BackfillInventoryDocument? baselineDocument) =>
        (baselineDocument?.RequireDigestionEntries() ?? [])
            .Select(CanonicalEntry)
            .ToHashSet(StringComparer.Ordinal);

    private static string? AdmissionGenreFinding(
        DigestionAlignmentMode mode,
        RepositorySnapshot candidateSnapshot,
        RepositorySnapshot? baselineSnapshot,
        DigestionLedgerSource candidateSource,
        DigestionLedgerSource? baselineSource,
        bool registeredAtomizer,
        TheoryAtomizerRules? atomizerRules,
        Func<string, TheoryAtomizer> atomizerResolver)
    {
        if (mode != DigestionAlignmentMode.Admission
            || candidateSource.Atomizer == AtomizerRegistry.NoAtomizerId
            || !registeredAtomizer
            || atomizerRules is null
            || AtomizerDecisionClosureEqualBaseline(
                candidateSnapshot,
                baselineSnapshot,
                candidateSource,
                baselineSource)
            || !candidateSnapshot.TryGetFile(candidateSource.SourcePath, out var sourceFile))
        {
            return null;
        }

        AtomizedTheoryDocument atomized;
        try
        {
            var atomize = atomizerResolver(candidateSource.Atomizer);
            atomized = atomize(sourceFile.RawBytes.AsSpan(), atomizerRules);
        }
        catch (Exception exception) when (
            exception is TheorySourceFormatException or DecoderFallbackException)
        {
            // The ordinary pass owns theory-source and UTF-8 decoding failures, so the probe
            // must not replace those outcomes with a genre finding.
            return null;
        }

        if (AtomizerIntegrityFailure(atomized, sourceFile.RawBytes.AsSpan()) is not null
            || !HasUniqueAstPaths(atomized.Claims)
            || atomized.Claims.Length == 0
            || atomized.GenreRegistryCheck.Kind != GenreRegistryCheckKind.Collected
            || atomized.UnregisteredGenres.IsEmpty)
        {
            return null;
        }

        return UnregisteredGenreFinding(candidateSource, atomized.UnregisteredGenres);
    }

    private static string UnregisteredGenreFinding(
        DigestionLedgerSource source,
        ImmutableArray<string> unregisteredGenres) =>
        $"source {source.SourceId} uses claim genres its dialect does not register: "
        + string.Join(", ", unregisteredGenres)
        + $". Register them in {TheoryAtomizerDataLoader.DataPath} or correct the volume.";

    private static bool AtomizerDecisionClosureEqualBaseline(
        RepositorySnapshot candidateSnapshot,
        RepositorySnapshot? baselineSnapshot,
        DigestionLedgerSource candidateSource,
        DigestionLedgerSource? baselineSource) =>
        baselineSnapshot is not null
        && baselineSource is not null
        && candidateSource.Atomizer == baselineSource.Atomizer
        && FileBytesEqual(
            candidateSnapshot,
            candidateSource.SourcePath,
            baselineSnapshot,
            baselineSource.SourcePath)
        && FileBytesEqual(
            candidateSnapshot,
            TheoryAtomizerDataLoader.DataPath,
            baselineSnapshot,
            TheoryAtomizerDataLoader.DataPath)
        // Atomizer implementations have no narrower stable content address. Whole-tree equality
        // proves their code closure is unchanged; any candidate change pays the cheap recheck.
        && RepositoryBytesEqual(candidateSnapshot, baselineSnapshot);

    private static bool RepositoryBytesEqual(
        RepositorySnapshot candidateSnapshot,
        RepositorySnapshot baselineSnapshot) =>
        candidateSnapshot.Files.Count == baselineSnapshot.Files.Count
        && candidateSnapshot.Files.All(candidate =>
            baselineSnapshot.Files.TryGetValue(candidate.Key, out var baseline)
            && candidate.Value.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan()));

    private static bool FileBytesEqual(
        RepositorySnapshot candidateSnapshot,
        string candidatePath,
        RepositorySnapshot baselineSnapshot,
        string baselinePath) =>
        candidateSnapshot.TryGetFile(candidatePath, out var candidate)
        && baselineSnapshot.TryGetFile(baselinePath, out var baseline)
        && candidate.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan());

    private static string CanonicalEntry(DigestionLedgerEntry entry) =>
        Convert.ToBase64String(BackfillInventoryWriter.WriteEntry(entry).AsSpan());

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


        var clausePlanFailure = ClausePlanIntegrityFailure(document);
        if (clausePlanFailure is not null)
        {
            return clausePlanFailure;
        }

        return null;
    }

    internal static bool FingerprintsMatch(DigestionFingerprints left, DigestionFingerprints right) =>
        left.RawSha256 == right.RawSha256
        || left.NormalizedSha256 == right.NormalizedSha256;

    private static bool HasUniqueAstPaths(ImmutableArray<DigestionAtom> claims) =>
        claims.Select(static claim => claim.AstPath).Distinct(StringComparer.Ordinal).Count()
        == claims.Length;

    private static bool EntryIdentityEqual(
        DigestionLedgerEntry candidate,
        DigestionLedgerEntry baseline) =>
        candidate.SourceId == baseline.SourceId
        && candidate.AtomId == baseline.AtomId
        && candidate.Fingerprints == baseline.Fingerprints;

    private static bool CoarseReplacementIdentityEqual(
        DigestionLedgerEntry candidate,
        DigestionLedgerEntry baseline) =>
        candidate.AstPath == "coarse/source"
        && baseline.AstPath == "coarse/source"
        && candidate.Boundary == baseline.Boundary
        && candidate.CasRef == baseline.CasRef
        && EntryIdentityEqual(candidate, baseline);

    private static DigestionLedgerEntry[] CoarseReplacementObligations(
        DigestionLedgerSource baseline,
        DigestionLedgerSource? candidate) =>
        baseline.Entries.Where(entry =>
            entry.AstPath == "coarse/source"
            && (candidate is null
                || !candidate.Entries.Any(candidateEntry =>
                    CoarseReplacementIdentityEqual(candidateEntry, entry))
                || baseline.AcknowledgedStale.Contains(entry.AtomId, StringComparer.Ordinal)
                || baseline.Atomizer != candidate.Atomizer
                || candidate.AcknowledgedStale.Contains(
                    entry.AtomId,
                    StringComparer.Ordinal)))
            .ToArray();
}
