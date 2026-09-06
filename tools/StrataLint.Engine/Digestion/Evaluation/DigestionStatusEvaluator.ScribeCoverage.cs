using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    private static void RequireScribeReceiptsForCoverageDelta(
        IEnumerable<EntryWork> work,
        IReadOnlySet<string> affectedAtomIds,
        IReadOnlyDictionary<string, DigestionLedgerEntry> baselineEntries,
        bool hasProtectedBase,
        ImmutableArray<string>.Builder findings)
    {
        // Compare edge values against protected-base data even in a producer full scan.
        // Unchanged missing receipts remain observable through VerifyScribeReceipts.
        foreach (var item in work.Where(item => affectedAtomIds.Contains(item.Entry.AtomId)))
        {
            var entry = item.Entry;
            baselineEntries.TryGetValue(entry.AtomId, out var baseline);
            foreach (var edge in entry.Coverage)
            {
                var applicability = item.ReceiptApplicabilities[edge.Gid];
                if (applicability is ReceiptApplicability.Failure failure)
                {
                    findings.Add($"entry {entry.AtomId} scribe-applicability-invalid: {edge.Gid}; {failure.Message}");
                    continue;
                }

                if (applicability is not ReceiptApplicability.Required
                    || !hasProtectedBase
                    || baseline?.Coverage.Contains(edge) == true
                    || entry.Receipts.Scribe.Count(receipt => receipt.Gid == edge.Gid) == 1)
                {
                    continue;
                }

                findings.Add($"entry {entry.AtomId} coverage-scribe-receipt-required: {edge.Gid}; "
                    + "new or changed coverage requires exactly one matching Scribe receipt");
            }
        }
    }

    private static ReceiptApplicability ClassifyReceipt(
        string gidText,
        CurrentEdgeValidation edge,
        RepositorySnapshot snapshot,
        LeanAxiomReport report,
        Lazy<FrozenStatementIndex> frozenStatements)
    {
        try
        {
            Gid.TryParse(gidText, out var gid);
            return ReceiptApplicability.Classify(gid, edge, snapshot, report, frozenStatements.Value);
        }
        catch (Exception exception) when (exception is FormatException or InvalidOperationException)
        {
            return new ReceiptApplicability.Failure(exception.Message);
        }
    }
}
