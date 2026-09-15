namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    internal static string UpstreamProbePath(DigestionLedgerEntry entry) =>
        "Meta/Digestion/upstream/" + entry.AtomId + ".lean";

    private static void VerifyUpstreamProbe(DigestionLedgerEntry entry, RepositorySnapshot snapshot,
        RawChangeSet? changes, bool authorityChanged, List<DigestionGap> gaps)
    {
        if (entry.Receipts.Upstream is not { } receipt) return;
        var path = UpstreamProbePath(entry);
        if (changes is not null && !authorityChanged && !PathChanged(changes, path)) return;
        string? detail;
        if (!snapshot.TryGetFile(path, out var probe)) detail = "missing";
        else
        {
            var actual = DigestionFingerprint.Compute(probe.RawBytes.AsSpan()).RawSha256;
            detail = actual == receipt.ProbeSha256 ? null : $"sha256 mismatch stored={receipt.ProbeSha256} actual={actual}";
        }
        if (detail is not null)
            gaps.Add(new DigestionGap("BACKFILL_UPSTREAM_PROBE", detail, DigestionGapSeverity.ReceiptIntegrityFailure));
    }
}
