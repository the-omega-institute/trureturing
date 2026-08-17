using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
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
        RawChangeSet? changes,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        if (changes is not null
            && !DigestionCasStore.EntryChanged(entry, changes)
            && !PathChanged(changes, entry.SourcePath)
            && !PathChanged(changes, TheoryAtomizerDataLoader.DataPath))
        {
            return true;
        }

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

        if (!TheoryAtomizerDataLoader.TryLoad(snapshot, out var atomizerRules))
        {
            // This tree predates the atomizer data surface, so the boundary cannot be re-derived
            // against it. Recording a gap here would make a harness carrying this loader reject a
            // tree the baseline harness admits, which conservative extension forbids. A tree that
            // DOES carry the data file gets the full check below, and admission separately
            // requires the file to exist (FILEMAP, registry, generated-artifact inventory), so
            // this branch cannot be reached by deleting it from a current tree.
            return true;
        }

        AtomizedTheoryDocument atomized;
        try
        {
            atomized = AtomizerRegistry.Atomize(
                entry.Atomizer,
                source.RawBytes.AsSpan(),
                atomizerRules);
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
        RawChangeSet? changes,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var receipts = UniqueByGid(entry.EntryLabel(), entry.Receipts.Coverage, static item => item.Gid, findings);
        var complete = true;
        foreach (var gid in entry.CoverageGids.Distinct(StringComparer.Ordinal))
        {
            if (!receipts.TryGetValue(gid, out var receipt))
            {
                gaps.Add(new DigestionGap("coverage-receipt-missing", gid));
                complete = false;
                continue;
            }

            var targetChanged = Gid.TryParse(gid, out var parsedGid)
                && PathChanged(changes, parsedGid.Path.Value);
            if (changes is not null
                && !DigestionCasStore.EntryChanged(entry, changes)
                && !targetChanged)
            {
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
        VerifiedScribeEmissions? verifiedEmissions,
        RawChangeSet? changes,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var receipts = UniqueByGid(entry.EntryLabel(), entry.Receipts.Scribe, static item => item.Gid, findings);
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
            var receiptInputChanged = changes is null
                || DigestionCasStore.EntryChanged(entry, changes)
                || PathChanged(changes, definitionPath)
                || PathChanged(changes, emissionPath)
                || parsedGid is not null && PathChanged(changes, parsedGid.Path.Value);
            ScribeEmissionRecord? verified = null;
            if (verifiedEmissions is null)
            {
                gaps.Add(new DigestionGap("scribe-emission-unverified", gid));
                complete = false;
            }
            else if (!verifiedEmissions.TryGet(documentGid, out var verifiedRecord))
            {
                gaps.Add(new DigestionGap("scribe-emission-missing", gid));
                complete = false;
            }
            else
            {
                verified = verifiedRecord;
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
                && receiptInputChanged
                && (receipt!.DefinitionSha256
                    != DigestionFingerprint.Compute(definition.RawBytes.AsSpan()).RawSha256
                    || verified is not null
                    && (verified.DefinitionPath != definitionPath
                        || verified.DefinitionSha256 != receipt.DefinitionSha256)))
            {
                gaps.Add(new DigestionGap("scribe-definition-mismatch", gid));
                complete = false;
            }

            if (hasReceipt
                && receiptInputChanged
                && verified is not null
                && (verified.EmissionPath != emissionPath
                    || verified.EmissionSha256 != receipt!.EmissionSha256))
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

    private static bool PathChanged(RawChangeSet? changes, string path) =>
        changes is null || changes.Paths.Any(changed => changed.Value == path);
}
