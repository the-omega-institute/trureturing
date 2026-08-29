using System.Collections.Immutable;

namespace StrataLint.Engine;

internal class FrozenLedgerReplacementRecognition
{
    protected FrozenLedgerReplacementRecognition(
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

internal sealed class FrozenLedgerIncrementalReplacementRecognition
    : FrozenLedgerReplacementRecognition
{
    private FrozenLedgerIncrementalReplacementRecognition(
        ImmutableHashSet<RepoPath> deletedAcceptedPaths,
        ImmutableHashSet<RepoPath> retainedModulePaths,
        RepoPath witnessPath,
        ImmutableHashSet<RepoPath> reanchoredModulePaths)
        : base(deletedAcceptedPaths, retainedModulePaths, witnessPath) =>
        ReanchoredModulePaths = reanchoredModulePaths;

    internal ImmutableHashSet<RepoPath> ReanchoredModulePaths { get; }

    internal static FrozenLedgerIncrementalReplacementRecognition? Recognize(
        FrozenLedgerBaseView baseView,
        RepositorySnapshot current,
        RawChangeSet changes,
        ImmutableArray<DagLedgerFileEvent> deltaEvents,
        FrozenMaterialCatalog candidateCatalog)
    {
        ArgumentNullException.ThrowIfNull(baseView);
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(candidateCatalog);

        var baseModulePaths = baseView.ActiveByPath.Keys.ToImmutableHashSet();
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
        var retainedModulePaths = baseModulePaths.Except(deletedModulePaths).ToImmutableHashSet();
        var changedStatementPaths = baseView.ActiveByPath
            .Where(item => !candidateCatalog.ByPath.TryGetValue(item.Key, out var candidate)
                || candidate.StatementId != item.Value.Material.StatementId)
            .Select(static item => item.Key)
            .ToImmutableHashSet();
        var deletedEventsResolvedExactly = baseView.Events.Count(item =>
                item.FreezePayload is not null && deletedAcceptedPaths.Contains(item.SourcePath))
            == deletedAcceptedPaths.Count;
        var retainedEventsUnchanged = baseView.Events
            .Where(item => !deletedAcceptedPaths.Contains(item.SourcePath))
            .All(item => current.TryGetFile(item.SourcePath.Value, out var candidate)
                && candidate.RawBytes.AsSpan().SequenceEqual(item.RawBytes.AsSpan()));
        var expectedAcceptedPaths = baseView.Events
            .Where(item => !deletedAcceptedPaths.Contains(item.SourcePath))
            .Select(static item => item.SourcePath)
            .Concat(deltaEvents.Select(static item => item.SourcePath))
            .ToImmutableHashSet();
        var currentAcceptedPaths = current.Files.Keys
            .Where(static path => FrozenLedgerChangeClassifier.IsAcceptedEventPath(path.Value))
            .ToImmutableHashSet();
        var acceptedChangesAreReplacementOnly = changes.Entries
            .Where(static change => FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value))
            .All(change => change.Kind switch
            {
                RawChangeKind.Deleted => deletedAcceptedPaths.Contains(change.Path),
                RawChangeKind.Added or RawChangeKind.Copied =>
                    deltaEvents.Any(item => item.SourcePath == change.Path),
                _ => false,
            });
        var witnessPath = deletedAcceptedPaths
            .Concat(deltaEvents.Select(static item => item.SourcePath))
            .MinBy(static path => path.Value, StringComparer.Ordinal);

        return !baseModulePaths.IsEmpty
            && !deletedModulePaths.IsEmpty
            && deletedModulePaths.Count < baseModulePaths.Count
            && witnessPath is not null
            && deletedEventsResolvedExactly
            && retainedEventsUnchanged
            && acceptedChangesAreReplacementOnly
            && currentAcceptedPaths.SetEquals(expectedAcceptedPaths)
            && newModulePaths.SetEquals(deletedModulePaths)
            && changedStatementPaths.SetEquals(deletedModulePaths)
                ? new FrozenLedgerIncrementalReplacementRecognition(
                    deletedAcceptedPaths,
                    retainedModulePaths,
                    witnessPath,
                    deletedModulePaths)
                : null;
    }
}
