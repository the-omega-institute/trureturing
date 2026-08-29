using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed class FrozenLedgerReplacementRecognition
{
    private FrozenLedgerReplacementRecognition(
        ImmutableHashSet<RepoPath> deletedAcceptedPaths)
    {
        DeletedAcceptedPaths = deletedAcceptedPaths;
        WitnessPath = deletedAcceptedPaths.MinBy(
            static path => path.Value,
            StringComparer.Ordinal)
            ?? throw new InvalidOperationException("recognized ledger replacement has no witness path");
    }

    internal ImmutableHashSet<RepoPath> DeletedAcceptedPaths { get; }

    internal RepoPath WitnessPath { get; }

    internal static FrozenLedgerReplacementRecognition? Recognize(
        FrozenLedgerBaseView baseView,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(baseView);
        ArgumentNullException.ThrowIfNull(changes);
        var baseAcceptedPaths = baseView.Events
            .Select(static item => item.SourcePath)
            .ToImmutableHashSet();
        var deletedAcceptedPaths = changes.Entries
            .Where(static change => change.Kind is RawChangeKind.Deleted
                && FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value))
            .Select(static change => change.Path)
            .ToImmutableHashSet();
        return !baseAcceptedPaths.IsEmpty
            && baseAcceptedPaths.SetEquals(deletedAcceptedPaths)
                ? new FrozenLedgerReplacementRecognition(deletedAcceptedPaths)
                : null;
    }
}
