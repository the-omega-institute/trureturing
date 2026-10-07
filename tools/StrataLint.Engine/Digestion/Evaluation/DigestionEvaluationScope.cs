namespace StrataLint.Engine;

// The evaluator has two deliberately named modes. FullScan is a caller-visible request to
// replay every historical predicate; ChangedSet scopes receipt and authority checks to the
// supplied repository delta.
internal enum DigestionEvaluationScope
{
    FullScan,
    ChangedSet,
}

internal static class DigestionEvaluationScopes
{
    internal static RawChangeSet? ResolveChanges(
        DigestionEvaluationScope scope,
        RawChangeSet? changes) => scope switch
        {
            DigestionEvaluationScope.FullScan => null,
            DigestionEvaluationScope.ChangedSet when changes is not null => changes,
            DigestionEvaluationScope.ChangedSet => throw new ArgumentException(
                "ChangedSet requires an explicit change set.",
                nameof(changes)),
            _ => throw new ArgumentOutOfRangeException(nameof(scope)),
        };
}
