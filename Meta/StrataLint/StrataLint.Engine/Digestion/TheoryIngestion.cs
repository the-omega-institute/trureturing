using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum DigestionFingerprintMatch
{
    Raw,
    Normalized,
}

internal sealed record SeenDigestionAtom(
    DigestionAtom Atom,
    string LedgerAtomId,
    DigestionFingerprintMatch Match);

internal sealed record ResidualDigestionAdmission(
    DigestionAtom Atom,
    string SuggestedAtomId,
    DigestionStatus ProjectedStatus);

internal sealed record TheoryIngestionResult(
    ImmutableArray<SeenDigestionAtom> Seen,
    ImmutableArray<ResidualDigestionAdmission> Residual);

internal static class TheoryIngestion
{
    internal static TheoryIngestionResult AdmitResidual(
        string atomizerId,
        ReadOnlySpan<byte> bytes,
        IEnumerable<DigestionLedgerEntry> ledger)
    {
        var registration = AtomizerRegistry.Require(atomizerId);
        return DigestionFingerprintSubtractor.Subtract(
            registration.Atomize(bytes),
            ledger,
            atomizerId,
            registration.ResidualPrefix);
    }
}

internal static class DigestionFingerprintSubtractor
{
    internal static TheoryIngestionResult Subtract(
        AtomizedTheoryDocument document,
        IEnumerable<DigestionLedgerEntry> ledger,
        string atomizer,
        string residualPrefix)
    {
        ArgumentNullException.ThrowIfNull(document);
        ArgumentNullException.ThrowIfNull(ledger);
        ArgumentException.ThrowIfNullOrWhiteSpace(atomizer);
        ArgumentException.ThrowIfNullOrWhiteSpace(residualPrefix);

        var candidates = ledger.Where(entry => entry.Atomizer == atomizer).ToArray();
        if (candidates.Any(static entry =>
                !DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.RawSha256)
                || !DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.NormalizedSha256)))
        {
            throw new FormatException($"{atomizer} ledger contains a noncanonical fingerprint");
        }

        var seen = ImmutableArray.CreateBuilder<SeenDigestionAtom>();
        var residual = ImmutableArray.CreateBuilder<ResidualDigestionAdmission>();
        var usedReceipts = new HashSet<string>(StringComparer.Ordinal);
        var unmatchedRawFingerprints = new HashSet<string>(StringComparer.Ordinal);
        var unmatchedNormalizedFingerprints = new HashSet<string>(StringComparer.Ordinal);
        foreach (var atom in document.Claims)
        {
            var matches = candidates
                .Select(entry => (Entry: entry, Match: Match(atom.Fingerprints, entry.Fingerprints)))
                .Where(static item => item.Match is not null)
                .ToArray();
            if (matches.Length > 1)
            {
                throw new FormatException(
                    $"ambiguous {atomizer} fingerprint match for {atom.AstPath}: "
                    + string.Join(',', matches.Select(static item => item.Entry.AtomId)));
            }

            if (matches.Length == 1)
            {
                var match = matches[0];
                if (!usedReceipts.Add(match.Entry.AtomId))
                {
                    throw new FormatException(
                        $"ambiguous {atomizer} receipt {match.Entry.AtomId} matches multiple incoming atoms");
                }

                seen.Add(new SeenDigestionAtom(atom, match.Entry.AtomId, match.Match!.Value));
                continue;
            }

            if (!unmatchedRawFingerprints.Add(atom.Fingerprints.RawSha256))
            {
                throw new FormatException(
                    $"ambiguous duplicate raw residual fingerprint in {atomizer}: {atom.AstPath}");
            }

            if (!unmatchedNormalizedFingerprints.Add(atom.Fingerprints.NormalizedSha256))
            {
                throw new FormatException(
                    $"ambiguous duplicate normalized residual fingerprint in {atomizer}: {atom.AstPath}");
            }

            residual.Add(new ResidualDigestionAdmission(
                atom,
                residualPrefix + "-residual-" + atom.Fingerprints.RawSha256["sha256:".Length..],
                new DigestionStatus(DigestionMigrationState.Residual, DigestionTruthState.Open)));
        }

        return new TheoryIngestionResult(seen.ToImmutable(), residual.ToImmutable());
    }

    private static DigestionFingerprintMatch? Match(
        DigestionFingerprints incoming,
        DigestionFingerprints ledger) =>
        incoming.RawSha256 == ledger.RawSha256
            ? DigestionFingerprintMatch.Raw
            : incoming.NormalizedSha256 == ledger.NormalizedSha256
                ? DigestionFingerprintMatch.Normalized
                : null;
}
