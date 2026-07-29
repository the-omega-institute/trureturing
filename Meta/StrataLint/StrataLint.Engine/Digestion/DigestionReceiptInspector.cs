using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal sealed record DigestionReceiptInspection(
    ImmutableArray<DigestionGap> Gaps,
    ImmutableArray<(string Gid, TruthState State)> TargetStates,
    bool LocalComplete,
    bool HasProgress);

internal static class DigestionReceiptInspector
{
    internal static DigestionReceiptInspection Inspect(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        RepositorySnapshot snapshot,
        LeanAxiomReport leanReport,
        IReadOnlyDictionary<RepoPath, TruthNode> nodes,
        ScribeEmissionAttestation scribeAttestation,
        VerifiedScribeEmissions? verifiedScribeEmissions,
        ImmutableArray<string>.Builder findings)
    {
        ArgumentNullException.ThrowIfNull(entry);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(leanReport);
        ArgumentNullException.ThrowIfNull(nodes);
        ArgumentNullException.ThrowIfNull(scribeAttestation);
        ArgumentNullException.ThrowIfNull(findings);

        var gaps = new List<DigestionGap>();
        var boundary = entry.Atomizer == AtomizerRegistry.NoAtomizerId
            && entry.Boundary is not null
                ? VerifyBoundary(entry, snapshot, gaps, findings)
                : VerifyStructuredAlignment(entry, alignment, gaps, findings);
        var targetStates = new List<(string Gid, TruthState State)>();
        var existingTargets = new Dictionary<string, RepositoryFile>(StringComparer.Ordinal);
        foreach (var gidText in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            if (!Gid.TryParse(gidText, out var gid)
                || !snapshot.TryGetFile(gid.Path.Value, out var target))
            {
                gaps.Add(new DigestionGap("target-gid-missing", gidText));
                continue;
            }

            if (!DeclarationExists(gid, leanReport, gaps))
            {
                continue;
            }

            existingTargets.Add(gidText, target);
            targetStates.Add((
                gidText,
                nodes.TryGetValue(target.Path, out var node) ? node.State : TruthState.Semantic));
        }

        if (entry.CoverageGids.Length == 0)
        {
            gaps.Add(new DigestionGap("coverage-gid-missing", entry.AtomId));
        }

        var coverage = VerifyCoverageReceipts(entry, existingTargets, gaps, findings);
        var scribe = VerifyScribeReceipts(
            entry,
            snapshot,
            scribeAttestation,
            verifiedScribeEmissions,
            gaps,
            findings);
        if (entry.Receipts.UnresolvedSubitems.Length > 0)
        {
            foreach (var subitem in entry.Receipts.UnresolvedSubitems)
            {
                gaps.Add(new DigestionGap("unresolved-subitem", subitem));
            }
        }

        var localComplete = boundary
            && existingTargets.Count == entry.CoverageGids.Distinct(StringComparer.Ordinal).Count()
            && entry.CoverageGids.Length > 0
            && coverage
            && scribe
            && entry.Receipts.UnresolvedSubitems.Length == 0;
        var hasProgress = existingTargets.Count > 0
            || entry.Receipts.Coverage.Length > 0
            || entry.Receipts.Scribe.Length > 0;
        return new DigestionReceiptInspection(
            gaps.ToImmutableArray(),
            targetStates.ToImmutableArray(),
            localComplete,
            hasProgress);
    }

    private static bool DeclarationExists(
        Gid gid,
        LeanAxiomReport leanReport,
        ICollection<DigestionGap> gaps)
    {
        if (gid.ToTarget() is not Target.Formal { Declaration: { } declaration } formal)
        {
            return true;
        }

        if (!leanReport.Files.TryGetValue(formal.Path, out var module)
            || !string.IsNullOrEmpty(module.Error))
        {
            gaps.Add(new DigestionGap("target-declaration-missing", gid.Value));
            return false;
        }

        var suffix = "." + declaration;
        var matches = module.Declarations.Count(candidate =>
            string.Equals(candidate.Name, declaration, StringComparison.Ordinal)
            || candidate.Name.EndsWith(suffix, StringComparison.Ordinal));
        if (matches == 1)
        {
            return true;
        }

        gaps.Add(new DigestionGap(
            matches == 0 ? "target-declaration-missing" : "target-declaration-ambiguous",
            gid.Value));
        return false;
    }

    private static bool VerifyStructuredAlignment(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        if (!DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.RawSha256)
            || !DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.NormalizedSha256))
        {
            findings.Add($"entry {entry.AtomId} fingerprints must use canonical sha256:<64 lowercase hex>");
            gaps.Add(new DigestionGap("fingerprint-invalid", entry.AtomId));
            return false;
        }

        switch (alignment)
        {
            case DigestionReceiptAlignment.Seen:
                return true;
            case DigestionReceiptAlignment.Stale:
                gaps.Add(new DigestionGap("stale-receipt-not-deletable", entry.AstPath));
                return false;
            default:
                gaps.Add(new DigestionGap("structural-alignment-rejected", entry.AstPath));
                return false;
        }
    }

    private static bool VerifyBoundary(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var boundary = entry.Boundary;
        if (boundary is null)
        {
            gaps.Add(new DigestionGap("boundary-not-reproducible", entry.AstPath));
            return false;
        }

        if (Path.GetFileName(entry.SourcePath).Contains(' ', StringComparison.Ordinal))
        {
            findings.Add($"source {entry.SourceId} filename contains spaces: {entry.SourcePath}");
        }

        if (!DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.RawSha256)
            || !DigestionFingerprint.IsCanonicalSha256(entry.Fingerprints.NormalizedSha256))
        {
            findings.Add($"entry {entry.AtomId} fingerprints must use canonical sha256:<64 lowercase hex>");
            gaps.Add(new DigestionGap("fingerprint-invalid", entry.AtomId));
            return false;
        }

        if (!snapshot.TryGetFile(entry.SourcePath, out var source))
        {
            gaps.Add(new DigestionGap("source-missing", entry.SourcePath));
            return false;
        }

        if (boundary.StartByte < 0
            || boundary.EndByte <= boundary.StartByte
            || boundary.EndByte > source.RawBytes.Length)
        {
            findings.Add(
                $"entry {entry.AtomId} byte span is outside {entry.SourcePath}; run make ingest");
            gaps.Add(new DigestionGap("boundary-span-invalid", boundary.AstPath));
            return false;
        }

        var storedSlice = source.RawBytes.AsSpan()[boundary.StartByte..boundary.EndByte];
        DigestionFingerprints fingerprints;
        try
        {
            fingerprints = DigestionFingerprint.Compute(storedSlice);
        }
        catch (DecoderFallbackException)
        {
            findings.Add(
                $"entry {entry.AtomId} boundary cuts invalid UTF-8 in {entry.SourcePath}; "
                + "run make ingest");
            gaps.Add(new DigestionGap("boundary-not-reproducible", boundary.AstPath));
            return false;
        }

        if (fingerprints != entry.Fingerprints)
        {
            findings.Add(
                $"entry {entry.AtomId} fingerprint disagrees with its source byte span; "
                + "run make ingest");
            gaps.Add(new DigestionGap("boundary-fingerprint-mismatch", boundary.AstPath));
            return false;
        }

        AtomizedTheoryDocument atomized;
        try
        {
            atomized = AtomizerRegistry.Atomize(entry.Atomizer, source.RawBytes.AsSpan());
        }
        catch (FormatException exception)
        {
            gaps.Add(new DigestionGap("boundary-not-reproducible", exception.Message));
            return false;
        }

        DigestionAtom atom;
        try
        {
            atom = atomized.ResolveClaim(boundary.AstPath);
        }
        catch (FormatException exception)
        {
            gaps.Add(new DigestionGap("boundary-not-reproducible", exception.Message));
            return false;
        }
        if (atom.StartByte != boundary.StartByte
            || atom.EndByte != boundary.EndByte
            || atom.Fingerprints != entry.Fingerprints)
        {
            gaps.Add(new DigestionGap("boundary-fingerprint-mismatch", boundary.AstPath));
            return false;
        }

        return true;
    }

    private static bool VerifyCoverageReceipts(
        DigestionLedgerEntry entry,
        IReadOnlyDictionary<string, RepositoryFile> targets,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var receipts = UniqueByGid(entry.AtomId, entry.Receipts.Coverage, static item => item.Gid, findings);
        var complete = true;
        foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            if (!receipts.TryGetValue(gid, out var receipt))
            {
                gaps.Add(new DigestionGap("coverage-receipt-missing", gid));
                complete = false;
                continue;
            }

            if (!targets.TryGetValue(gid, out var target)
                || receipt.SourceSha256 != entry.Fingerprints.RawSha256
                || receipt.TargetSha256 != DigestionFingerprint.Compute(target.RawBytes.AsSpan()).RawSha256)
            {
                gaps.Add(new DigestionGap("coverage-receipt-mismatch", gid));
                complete = false;
            }
        }

        foreach (var extra in receipts.Keys.Except(entry.CoverageGids, StringComparer.Ordinal))
        {
            findings.Add($"entry {entry.AtomId} has an extra coverage receipt for {extra}");
            complete = false;
        }

        return complete;
    }

    private static bool VerifyScribeReceipts(
        DigestionLedgerEntry entry,
        RepositorySnapshot snapshot,
        ScribeEmissionAttestation attestation,
        VerifiedScribeEmissions? verifiedEmissions,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var receipts = UniqueByGid(entry.AtomId, entry.Receipts.Scribe, static item => item.Gid, findings);
        var complete = true;
        foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            var hasReceipt = receipts.TryGetValue(gid, out var receipt);
            if (!hasReceipt)
            {
                gaps.Add(new DigestionGap("scribe-receipt-missing", gid));
                complete = false;
            }

            var documentGid = ScribeEmissionAttestation.DocumentGid(gid);
            var definitionPath = ScribeEmissionAttestation.DefinitionPath(documentGid);
            var emissionPath = ScribeEmissionAttestation.EmissionPath(documentGid);
            var selectsDeclaration = Gid.TryParse(gid, out var parsedGid)
                && parsedGid.ToTarget() is Target.Formal { Declaration: not null };
            var hasAttestation = attestation.TryGet(documentGid, out var emitted);
            if (!hasAttestation)
            {
                gaps.Add(new DigestionGap("scribe-attestation-missing", gid));
                complete = false;
            }

            ScribeEmissionRecord? verified = null;
            if (verifiedEmissions is not null
                && verifiedEmissions.TryGet(documentGid, out var verifiedRecord))
            {
                verified = verifiedRecord;
            }
            else
            {
                gaps.Add(new DigestionGap("scribe-emission-unverified", gid));
                complete = false;
            }

            if (selectsDeclaration
                && verifiedEmissions is not null
                && !verifiedEmissions.ReferencesDeclaration(gid))
            {
                gaps.Add(new DigestionGap("scribe-declaration-reference-missing", gid));
                complete = false;
            }

            if (!snapshot.TryGetFile(definitionPath, out var definition))
            {
                gaps.Add(new DigestionGap("scribe-definition-missing", gid));
                complete = false;
            }
            else if (hasReceipt
                && (receipt!.DefinitionSha256
                    != DigestionFingerprint.Compute(definition.RawBytes.AsSpan()).RawSha256
                    || hasAttestation
                    && (emitted!.DefinitionPath != definitionPath
                        || emitted.DefinitionSha256 != receipt.DefinitionSha256)
                    || verified is not null
                    && (verified.DefinitionPath != definitionPath
                        || verified.DefinitionSha256 != receipt.DefinitionSha256)))
            {
                gaps.Add(new DigestionGap("scribe-definition-mismatch", gid));
                complete = false;
            }

            if (!snapshot.TryGetFile(emissionPath, out var emission))
            {
                gaps.Add(new DigestionGap("scribe-emission-missing", gid));
                complete = false;
            }
            else if (hasReceipt
                && (receipt!.EmissionSha256
                    != DigestionFingerprint.Compute(emission.RawBytes.AsSpan()).RawSha256
                    || hasAttestation
                    && (emitted!.EmissionPath != emissionPath
                        || emitted.EmissionSha256 != receipt.EmissionSha256)
                    || verified is not null
                    && (verified.EmissionPath != emissionPath
                        || verified.EmissionSha256 != receipt.EmissionSha256)))
            {
                gaps.Add(new DigestionGap("scribe-emission-mismatch", gid));
                complete = false;
            }
        }

        foreach (var extra in receipts.Keys.Except(entry.CoverageGids, StringComparer.Ordinal))
        {
            findings.Add($"entry {entry.AtomId} has an extra Scribe receipt for {extra}");
            complete = false;
        }

        return complete;
    }

    private static Dictionary<string, T> UniqueByGid<T>(
        string label,
        IEnumerable<T> values,
        Func<T, string> gid,
        ImmutableArray<string>.Builder findings)
    {
        var result = new Dictionary<string, T>(StringComparer.Ordinal);
        foreach (var value in values)
        {
            var key = gid(value);
            if (!result.TryAdd(key, value))
            {
                findings.Add($"entry {label} has duplicate receipt for {key}");
            }
        }

        return result;
    }
}
