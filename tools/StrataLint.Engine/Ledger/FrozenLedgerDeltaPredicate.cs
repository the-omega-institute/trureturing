namespace StrataLint.Engine;

internal static class FrozenLedgerDeltaPredicate
{
    internal static bool HasLedgerDelta(
        RawChangeSet changes,
        IReadOnlySet<string> leanReportProducerPaths)
    {
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(leanReportProducerPaths);
        return changes.Entries.Any(change =>
            FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value)
            || IsEnvironmentInput(change.Path.Value)
            || IsManagedLeanSource(change.Path.Value)
            || leanReportProducerPaths.Contains(change.Path.Value));
    }

    internal static bool IsEnvironmentInput(string path) =>
        path is "lean-toolchain"
            or "lakefile.toml"
            or "lakefile.lean"
            or "lake-manifest.json";

    internal static bool IsManagedLeanSource(string path) =>
        path == "Trureturing.lean"
        || path.StartsWith("D5/", StringComparison.Ordinal)
            && path.EndsWith(".lean", StringComparison.Ordinal);
}
