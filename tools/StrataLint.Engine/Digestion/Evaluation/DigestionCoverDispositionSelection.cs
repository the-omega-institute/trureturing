namespace StrataLint.Engine;

internal enum DigestionCoverDispositionSelection
{
    Available,
    Withheld,
    Retry,
}

internal static class DigestionCoverDispositionSelector
{
    internal const string WithholdReason = "cover-disposition";

    internal static bool IsWithheld(DigestionLedgerEntry entry) =>
        Classify(entry, retryDispositions: false) == DigestionCoverDispositionSelection.Withheld;

    internal static DigestionCoverDispositionSelection Classify(
        DigestionLedgerEntry entry,
        bool retryDispositions)
    {
        ArgumentNullException.ThrowIfNull(entry);
        if (entry.Receipts.CoverDisposition is null)
        {
            return DigestionCoverDispositionSelection.Available;
        }

        return retryDispositions
            ? DigestionCoverDispositionSelection.Retry
            : DigestionCoverDispositionSelection.Withheld;
    }
}
