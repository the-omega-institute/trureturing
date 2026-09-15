using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DigestStatusCommand
{
    private static SortedDictionary<string, int> StatusCounts(DigestionLedgerEvaluation evaluation)
    {
        var counts = new SortedDictionary<string, int>(StringComparer.Ordinal);
        foreach (var migration in new[] { DigestionMigrationState.Residual, DigestionMigrationState.Partial, DigestionMigrationState.Absorbed })
            foreach (var truth in new[] { DigestionTruthState.Open, DigestionTruthState.Closed, DigestionTruthState.Tail })
                counts[DigestionStatusNames.Migration(migration) + "_" + DigestionStatusNames.Truth(truth)] = 0;
        counts["nonpropositional_inapplicable"] = 0;
        counts["upstream_closed"] = 0;
        foreach (var item in evaluation.Entries)
            counts[DigestionStatusNames.Migration(item.DerivedStatus.Migration) + "_" + DigestionStatusNames.Truth(item.DerivedStatus.Truth)]++;
        return counts;
    }

    private static int FormalizableTotal(DigestionLedgerEvaluation evaluation) => evaluation.Entries.Count(static item =>
        item.DerivedStatus.Migration is not (DigestionMigrationState.Upstream or DigestionMigrationState.Nonpropositional));
}
