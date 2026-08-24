using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class LedgerWriteReceiptIntegrityGate
{
    internal static void RequireNoNewFailures(
        DigestionLedgerEvaluation evaluation,
        IEnumerable<DigestionReceiptIntegrityGapIdentity> forkPointIdentities)
    {
        var newGaps = DigestionReceiptIntegrity.NewFailureIdentities(
            forkPointIdentities,
            evaluation);
        if (evaluation.Findings.Length == 0 && newGaps.Length == 0)
        {
            return;
        }

        throw new InvalidOperationException(
            "digest status is invalid: "
            + string.Join(
                "; ",
                evaluation.Findings.Concat(
                    newGaps.Select(DigestionReceiptIntegrity.Render))));
    }
}
