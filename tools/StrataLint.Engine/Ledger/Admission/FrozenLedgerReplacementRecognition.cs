using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed class FrozenLedgerReplacementRecognition
{
    private FrozenLedgerReplacementRecognition(
        ImmutableHashSet<RepoPath> deletedAcceptedPaths,
        ImmutableHashSet<RepoPath> retainedModulePaths,
        RepoPath witnessPath)
    {
        DeletedAcceptedPaths = deletedAcceptedPaths;
        RetainedModulePaths = retainedModulePaths;
        WitnessPath = witnessPath;
    }

    internal ImmutableHashSet<RepoPath> DeletedAcceptedPaths { get; }

    internal ImmutableHashSet<RepoPath> RetainedModulePaths { get; }

    internal RepoPath WitnessPath { get; }

    internal static FrozenLedgerReplacementRecognition? Recognize(
        FrozenLedgerBaseView baseView,
        RepositorySnapshot current,
        RawChangeSet changes,
        ImmutableArray<DagLedgerFileEvent> deltaEvents)
    {
        ArgumentNullException.ThrowIfNull(baseView);
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(changes);
        var baseModulePaths = baseView.ActiveByPath.Keys.ToImmutableHashSet();
        var retainedModulePaths = baseView.Events
            .Where(item => item.FreezePayload is not null
                && current.TryGetFile(item.SourcePath.Value, out var candidate)
                && candidate.RawBytes.AsSpan().SequenceEqual(item.RawBytes.AsSpan()))
            .Select(static item => RepoPath.CreateKnown(item.FreezePayload!.DescriptorSelector))
            .ToImmutableHashSet();
        var deletedAcceptedPaths = changes.Entries
            .Where(static change => change.Kind is RawChangeKind.Deleted
                && FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value))
            .Select(static change => change.Path)
            .ToImmutableHashSet();
        var deletedModulePaths = baseView.Events
            .Where(item => item.FreezePayload is not null
                && deletedAcceptedPaths.Contains(item.SourcePath))
            .Select(static item => RepoPath.CreateKnown(item.FreezePayload!.DescriptorSelector))
            .ToImmutableHashSet();
        var newModulePaths = deltaEvents
            .Where(static item => item.EventType == "Freeze")
            .Select(static item => item.DescriptorPath)
            .ToImmutableHashSet();
        var witnessPath = deletedAcceptedPaths
            .Concat(deltaEvents.Select(static item => item.SourcePath))
            .MinBy(static path => path.Value, StringComparer.Ordinal);

        return !baseModulePaths.IsEmpty
            && witnessPath is not null
            && !retainedModulePaths.Overlaps(newModulePaths)
            && deletedModulePaths.SetEquals(baseModulePaths.Except(retainedModulePaths))
                ? new FrozenLedgerReplacementRecognition(
                    deletedAcceptedPaths,
                    retainedModulePaths,
                    witnessPath)
                : null;
    }
}
