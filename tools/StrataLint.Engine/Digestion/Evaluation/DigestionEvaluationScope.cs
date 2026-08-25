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
        var callerDirectoryEnd = callerImplementationPath.LastIndexOf('/');
        var callerDirectory = callerDirectoryEnd < 0
            ? string.Empty
            : callerImplementationPath[..(callerDirectoryEnd + 1)];
        return !changes.Paths.Any()
            || changes.Paths.Any(path =>
                StrataLintEngineBuildInputs.Contains(path.Value)
                || IsCallerImplementationPath(
                    path.Value,
                    callerImplementationPath,
                    callerDirectory))
            ? DigestionEvaluationScope.FullScan
            : DigestionEvaluationScope.ChangedSet;
    }

    private static bool IsCallerImplementationPath(
        string path,
        string callerImplementationPath,
        string callerDirectory) =>
        string.Equals(path, callerImplementationPath, StringComparison.Ordinal)
        || (callerDirectory.Length > 0
            && path.StartsWith(callerDirectory, StringComparison.Ordinal)
            && path.EndsWith(".cs", StringComparison.Ordinal)
            && path.AsSpan(callerDirectory.Length).IndexOf('/') < 0);

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
