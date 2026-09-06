using System.Collections.Immutable;

namespace StrataLint.Engine;

internal abstract class FrozenLedgerReplacementRecognition;

internal sealed class FrozenLedgerIncrementalReplacementRecognition
    : FrozenLedgerReplacementRecognition
{
    private FrozenLedgerIncrementalReplacementRecognition(
        ImmutableHashSet<RepoPath> reanchoredModulePaths,
        ImmutableHashSet<RepoPath> changedStatementModulePaths)
    {
        ReanchoredModulePaths = reanchoredModulePaths;
        ChangedStatementModulePaths = changedStatementModulePaths;
    }

    internal ImmutableHashSet<RepoPath> ReanchoredModulePaths { get; }

    internal ImmutableHashSet<RepoPath> ChangedStatementModulePaths { get; }

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
        var changedStatementPaths = baseView.ActiveByPath
            .Where(item => !candidateCatalog.ByPath.TryGetValue(item.Key, out var candidate)
                || candidate.StatementId != item.Value.Material.StatementId)
            .Select(static item => item.Key)
            .ToImmutableHashSet();
        var expectedReplacementPaths = FrozenLedgerReplacementClosure.DescendantsFrom(
            baseView,
            changedStatementPaths);
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
        return !baseModulePaths.IsEmpty
            && !deletedModulePaths.IsEmpty
            && deletedEventsResolvedExactly
            && retainedEventsUnchanged
            && acceptedChangesAreReplacementOnly
            && currentAcceptedPaths.SetEquals(expectedAcceptedPaths)
            && newModulePaths.SetEquals(deletedModulePaths)
            && !changedStatementPaths.IsEmpty
            && changedStatementPaths.IsSubsetOf(deletedModulePaths)
            && deletedModulePaths.SetEquals(expectedReplacementPaths)
                ? new FrozenLedgerIncrementalReplacementRecognition(
                    deletedModulePaths,
                    changedStatementPaths)
                : null;
    }
}

internal static class FrozenLedgerReplacementClosure
{
    internal static ImmutableHashSet<RepoPath> DescendantsFrom(
        FrozenLedgerBaseView baseView,
        IEnumerable<RepoPath> seedPaths)
    {
        ArgumentNullException.ThrowIfNull(baseView);
        ArgumentNullException.ThrowIfNull(seedPaths);

        var pathByIdentity = new Dictionary<string, RepoPath>(StringComparer.Ordinal);
        foreach (var (path, entry) in baseView.ActiveByPath)
        {
            AddIdentity(entry.EventHash, path);
            AddIdentity(entry.Material.FrozenNodeId.Value, path);
        }

        var dependents = new Dictionary<RepoPath, HashSet<RepoPath>>();
        foreach (var (path, entry) in baseView.ActiveByPath)
        {
            foreach (var prerequisite in entry.Material.PrerequisiteFrozenNodeIds)
            {
                if (!pathByIdentity.TryGetValue(prerequisite.Value, out var dependencyPath))
                {
                    continue;
                }

                if (!dependents.TryGetValue(dependencyPath, out var directDependents))
                {
                    directDependents = [];
                    dependents.Add(dependencyPath, directDependents);
                }

                directDependents.Add(path);
            }
        }

        var closure = seedPaths.ToHashSet();
        var pending = new Queue<RepoPath>(closure.OrderBy(
            static path => path.Value,
            StringComparer.Ordinal));
        while (pending.TryDequeue(out var path))
        {
            if (!dependents.TryGetValue(path, out var directDependents))
            {
                continue;
            }

            foreach (var dependent in directDependents.OrderBy(
                static item => item.Value,
                StringComparer.Ordinal))
            {
                if (closure.Add(dependent))
                {
                    pending.Enqueue(dependent);
                }
            }
        }

        return closure.ToImmutableHashSet();

        void AddIdentity(string identity, RepoPath path)
        {
            if (pathByIdentity.TryGetValue(identity, out var existing) && existing != path)
            {
                throw new FormatException(
                    $"trusted frozen ledger identity {identity} resolves to multiple modules");
            }

            pathByIdentity[identity] = path;
        }
    }
}
