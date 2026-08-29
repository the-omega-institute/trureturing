using System.Collections.Immutable;
using System.Security.Cryptography;
using System.Text;

namespace StrataLint.Engine;

internal static partial class DigestionLedgerAligner
{
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
        ISet<string> suggestedAtomIds,
        IReadOnlySet<string>? occurrenceQualifiedStems = null)
    {
        var stem = registration.ResidualPrefix
            + $"-{kind}-"
            + atom.Fingerprints.RawSha256["sha256:".Length..];
        if (suggestedAtomIds.Add(stem))
        {
            return stem;
        }

        // Generic atomization can legitimately expose the same CAS content at a new locator
        // after a structural parser change (or at several locators in one source). Keep the
        // legacy ID untouched and qualify only the new residual occurrence. Other atomizers
        // retain their stricter collision refusal, notably the unregistered-genre path.
        var qualifyGenericCollision = registration.ResidualPrefix == GenericAtomizer.ResidualPrefix;
        if (!qualifyGenericCollision
            && (occurrenceQualifiedStems is null || !occurrenceQualifiedStems.Contains(stem)))
        {
            return stem;
        }

        var occurrenceBytes = Encoding.UTF8.GetBytes(source.SourceId + "\0" + atom.AstPath);
        var occurrence = Convert.ToHexStringLower(SHA256.HashData(occurrenceBytes));
        var qualified = stem + "-" + occurrence;
        suggestedAtomIds.Add(qualified);
        return qualified;
    }

    private static bool IsExactGenreResolution(
        string atomizer,
        string token,
        string openAstPath,
        string canonicalAstPath,
        TheoryAtomizerRules rules)
    {
        if (canonicalAstPath.StartsWith(UnregisteredGenreLocator.Prefix, StringComparison.Ordinal))
        {
            return false;
        }

        if (AtomizerRegistry.IsDeclaredDialect(atomizer))
        {
            var dialectId = atomizer[DeclaredDialectAtomizer.IdPrefix.Length..];
            if (!rules.Dialects.TryGetValue(dialectId, out var dialect))
            {
                return false;
            }

            var genre = dialect.Genres.FirstOrDefault(mapping => mapping.Token == token);
            genre ??= GenreSuffixResolver.Resolve(token, dialect.GenreSuffixes);
            return genre is not null
                && NumberedKindMatches(genre.Value, openAstPath, canonicalAstPath);
        }

        return atomizer switch
        {
            AtomizerRegistry.GictId => rules.GictGenres.Any(mapping =>
                mapping.Token == token
                && NumberedKindMatches(mapping.Value, openAstPath, canonicalAstPath)),
            AtomizerRegistry.PzgId => rules.PzgGenres.Any(mapping =>
                mapping.Token == token
                && NumberedKindMatches(mapping.Value, openAstPath, canonicalAstPath)),
            AtomizerRegistry.ConeId => rules.ConeClaimPrefixes.Any(mapping =>
                mapping.Token.Split('|').Contains(token, StringComparer.Ordinal)
                && mapping.Value.Split('|').Any(template =>
                    string.Equals(
                        template.Replace(
                            "{number}",
                            openAstPath[(openAstPath.LastIndexOf('/') + 1)..],
                            StringComparison.Ordinal),
                        canonicalAstPath,
                        StringComparison.Ordinal))),
            AtomizerRegistry.ObserverId => rules.ObserverClaimPrefixes.Any(mapping =>
                mapping.Token == token && mapping.Value == canonicalAstPath),
            _ => false,
        };
    }

    private static bool NumberedKindMatches(
        string kind,
        string openAstPath,
        string canonicalAstPath) => string.Equals(
            kind + openAstPath[openAstPath.LastIndexOf('/')..],
            canonicalAstPath,
            StringComparison.Ordinal);

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
                || HasAdapterFineReceipt(candidate)
                || candidate.AcknowledgedStale.Contains(
                    entry.AtomId,
                    StringComparer.Ordinal)))
            .ToArray();

    private static bool HasAdapterFineReceipt(DigestionLedgerSource source) =>
        AtomizerRegistry.IsRegistered(source.Atomizer)
        && source.Entries.Any(static entry =>
            entry.AstPath != "coarse/source");
}
