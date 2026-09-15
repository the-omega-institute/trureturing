namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    private static bool IsChainClosed(DigestionMigrationState migration) =>
        migration is DigestionMigrationState.Absorbed or DigestionMigrationState.Nonpropositional;

    private static bool HasNonpropositionalReceipt(DigestionLedgerEntry entry) =>
        entry.Receipts.Nonpropositional is { IsValid: true }
        && entry.Coverage.IsEmpty
        && entry.Receipts.Quarantine is null
        && entry.Receipts.CoverDisposition is null
        && entry.Receipts.UnresolvedSubitems.IsEmpty;
}
