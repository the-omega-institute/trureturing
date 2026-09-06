using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    private static void RequireScribeReceiptsForCoverageDelta(
        IEnumerable<DigestionLedgerEntry> entries,
        IReadOnlyDictionary<string, DigestionLedgerEntry> baselineEntries,
        ImmutableArray<string>.Builder findings)
    {
        // Compare edge values against protected-base data even in a producer full scan.
        // Unchanged missing receipts remain observable through VerifyScribeReceipts.
        foreach (var entry in entries)
        {
            baselineEntries.TryGetValue(entry.AtomId, out var baseline);
            foreach (var edge in entry.Coverage)
            {
                if (baseline?.Coverage.Contains(edge) == true
                    || entry.Receipts.Scribe.Count(receipt => receipt.Gid == edge.Gid) == 1)
                {
                    continue;
                }

                findings.Add($"entry {entry.AtomId} coverage-scribe-receipt-required: {edge.Gid}; "
                    + "new or changed coverage requires exactly one matching Scribe receipt");
            }
        }
    }
}
