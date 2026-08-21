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
    internal static DigestionEvaluationScope ForChanges(
        RawChangeSet changes,
        string callerImplementationPath)
    {
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentException.ThrowIfNullOrWhiteSpace(callerImplementationPath);
        return changes.Paths.Any(path =>
                StrataLintEngineBuildInputs.Contains(path.Value)
                || string.Equals(path.Value, callerImplementationPath, StringComparison.Ordinal))
            ? DigestionEvaluationScope.FullScan
            : DigestionEvaluationScope.ChangedSet;
    }
}
