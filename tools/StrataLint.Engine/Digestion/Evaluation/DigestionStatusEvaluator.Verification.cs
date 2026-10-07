using System.Collections.Immutable;

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
            if (edge.TargetStatementId is null)
            {
                complete = false;
                continue;
            }

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

    private static bool PathChanged(RawChangeSet? changes, string path) =>
        changes is null || changes.Paths.Any(changed => changed.Value == path);
}
