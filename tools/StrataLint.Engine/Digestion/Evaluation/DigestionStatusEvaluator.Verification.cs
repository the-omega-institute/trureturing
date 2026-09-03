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
            gaps.Add(new DigestionGap(
                "fingerprint-invalid",
                entry.AtomId,
                DigestionGapSeverity.NonFatal));
            return false;
        }

        switch (alignment)
        {
            case DigestionReceiptAlignment.Seen:
                return true;
            case DigestionReceiptAlignment.Stale:
                gaps.Add(new DigestionGap(
                    "stale-receipt-not-deletable",
                    entry.AtomId,
                    DigestionGapSeverity.NonFatal));
                return false;
            default:
                gaps.Add(new DigestionGap(
                    "structural-alignment-rejected",
                    entry.AtomId,
                    DigestionGapSeverity.NonFatal));
                return false;
        }
    }

    private static bool VerifyCoverageEdges(
        DigestionLedgerEntry entry,
        IReadOnlyDictionary<string, CurrentEdgeValidation> validations,
        ICollection<DigestionGap> gaps,
        ImmutableArray<string>.Builder findings)
    {
        var edges = UniqueByGid(entry.EntryLabel(), entry.Coverage, static item => item.Gid, findings);
        var complete = true;
        foreach (var (gid, edge) in edges)
        {
            var expectedTarget = validations.GetValueOrDefault(gid)?.TargetStatementId;
            if (!string.Equals(edge.TargetStatementId, expectedTarget, StringComparison.Ordinal))
            {
                gaps.Add(new DigestionGap(
                    "coverage-target-mismatch",
                    gid,
                    DigestionGapSeverity.ReceiptIntegrityFailure));
                complete = false;
            }
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
                gaps.Add(new DigestionGap(
                    "scribe-receipt-missing",
                    gid,
                    DigestionGapSeverity.NonFatal));
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
                gaps.Add(new DigestionGap(
                    "scribe-emission-unverified",
                    gid,
                    DigestionGapSeverity.NonFatal));
                complete = false;
            }
            else if (!verifiedEmissions.TryGet(documentGid, out var verifiedRecord))
            {
                gaps.Add(new DigestionGap(
                    "scribe-emission-missing",
                    gid,
                    DigestionGapSeverity.NonFatal));
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
                gaps.Add(new DigestionGap(
                    "scribe-declaration-reference-missing",
                    gid,
                    DigestionGapSeverity.NonFatal));
                complete = false;
            }

            if (!snapshot.TryGetFile(definitionPath, out var definition))
            {
                gaps.Add(new DigestionGap(
                    "scribe-definition-missing",
                    gid,
                    DigestionGapSeverity.NonFatal));
                complete = false;
            }
            // Binds scribe.definition_sha256 to both the definition bytes and verified Scribe
            // record. This guard does not bind emission, coverage, or projected_status.
            else if (hasReceipt
                && receiptInputChanged
                && (receipt!.DefinitionSha256
                    != DigestionFingerprint.Compute(definition.RawBytes.AsSpan()).RawSha256
                    || verified is not null
                    && (verified.DefinitionPath != definitionPath
                        || verified.DefinitionSha256 != receipt.DefinitionSha256)))
            {
                gaps.Add(new DigestionGap(
                    "scribe-definition-mismatch",
                    gid,
                    DigestionGapSeverity.ReceiptIntegrityFailure));
                complete = false;
            }

            // Binds scribe.emission_sha256 to the verified Scribe emission record. This guard
            // does not bind definition, coverage, or projected_status.
            if (hasReceipt
                && receiptInputChanged
                && verified is not null
                && (verified.EmissionPath != emissionPath
                    || verified.EmissionSha256 != receipt!.EmissionSha256))
            {
                gaps.Add(new DigestionGap(
                    "scribe-emission-mismatch",
                    gid,
                    DigestionGapSeverity.ReceiptIntegrityFailure));
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
