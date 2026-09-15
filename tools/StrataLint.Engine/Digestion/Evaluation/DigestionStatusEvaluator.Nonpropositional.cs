namespace StrataLint.Engine;

internal static partial class DigestionStatusEvaluator
{
    private static bool IsChainClosed(DigestionMigrationState migration) =>
        migration is DigestionMigrationState.Absorbed or DigestionMigrationState.Nonpropositional or DigestionMigrationState.Upstream;

    private static bool HasUpstreamReceipt(DigestionLedgerEntry entry) =>
        entry.Receipts.Upstream is { IsValid: true }
        && entry.Receipts.Nonpropositional is null
        && entry.Coverage.IsEmpty
        && entry.Receipts.Quarantine is null
        && entry.Receipts.CoverDisposition is null
        && entry.Receipts.UnresolvedSubitems.IsEmpty;

    private static bool HasNonpropositionalReceipt(DigestionLedgerEntry entry) =>
        entry.Receipts.Nonpropositional is { IsValid: true }
        && entry.Receipts.Upstream is null
        && entry.Coverage.IsEmpty
        && entry.Receipts.Quarantine is null
        && entry.Receipts.CoverDisposition is null
        && entry.Receipts.UnresolvedSubitems.IsEmpty;
}
