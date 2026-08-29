using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record FrozenLedgerAdmissionPreparation(
    FrozenLedgerBaseView BaseView,
    ImmutableArray<DagLedgerFileEvent> DeltaEvents,
    ImmutableHashSet<string> LeanReportProducerPaths,
    FrozenLedgerReplacementRecognition? Replacement = null);

internal sealed record FrozenLedgerAdmissionFailure(
    ImmutableArray<RepoPath> AffectedPaths,
    ImmutableArray<RepoPath> DeltaWitnessPaths,
    string Message);

internal sealed class FrozenLedgerAdmissionScope
{
    private FrozenLedgerAdmissionScope(
        ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> witnessesByPath)
    {
        WitnessesByPath = witnessesByPath;
    }

    internal ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> WitnessesByPath { get; }

    internal ImmutableHashSet<RepoPath> Paths => WitnessesByPath.Keys.ToImmutableHashSet();

    internal ImmutableArray<RepoPath> WitnessesFor(RepoPath path) =>
        WitnessesByPath.TryGetValue(path, out var witnesses)
            ? witnesses.OrderBy(static item => item.Value, StringComparer.Ordinal).ToImmutableArray()
            : throw new InvalidOperationException(
                $"frozen-ledger admission scope lost the delta witness for {path.Value}");

    internal static FrozenLedgerAdmissionScope Create(
        RawChangeSet changes,
        FrozenLedgerAdmissionPreparation preparation,
        IReadOnlyDictionary<RepoPath, TruthState> states,
        IReadOnlyDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency)
    {
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(preparation);
        ArgumentNullException.ThrowIfNull(states);
        ArgumentNullException.ThrowIfNull(adjacency);
        var witnesses = new Dictionary<RepoPath, HashSet<RepoPath>>();
        var allChanges = changes.Entries
            .Where(change => change.Path.Value == "Trureturing.lean"
                || FrozenLedgerDeltaPredicate.IsEnvironmentInput(change.Path.Value)
                || FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(change.Path.Value)
                || preparation.LeanReportProducerPaths.Contains(change.Path.Value))
            .Select(static change => change.Path)
            .ToImmutableHashSet();
        var currentClosed = states
            .Where(static item => item.Value is TruthState.Closed)
            .Select(static item => item.Key)
            .ToImmutableHashSet();
        if (!allChanges.IsEmpty)
        {
            foreach (var path in currentClosed.Union(preparation.BaseView.ActiveByPath.Keys))
            {
                Add(path, allChanges);
            }
        }

        foreach (var change in changes.Entries.Where(static change =>
            change.Path.Value.StartsWith("D5/", StringComparison.Ordinal)
            && change.Path.Value.EndsWith(".lean", StringComparison.Ordinal)))
        {
            Add(change.Path, [change.Path]);
        }

        foreach (var item in preparation.DeltaEvents)
        {
            Add(item.DescriptorPath, [item.SourcePath]);
        }

        if (preparation.Replacement is { } replacement)
        {
            foreach (var path in currentClosed.Union(preparation.BaseView.ActiveByPath.Keys))
            {
                Add(path, [replacement.WitnessPath]);
            }
        }

        var currentDependents = ReverseDependencies(adjacency);
        var baseDependents = BaseReverseDependencies(preparation.BaseView);
        var queue = new Queue<RepoPath>(witnesses.Keys);
        while (queue.TryDequeue(out var changed))
        {
            var changedWitnesses = witnesses[changed];
            foreach (var dependent in DependentsOf(changed, currentDependents, baseDependents))
            {
                if (!witnesses.TryGetValue(dependent, out var dependentWitnesses))
                {
                    dependentWitnesses = new HashSet<RepoPath>();
                    witnesses.Add(dependent, dependentWitnesses);
                }

                var before = dependentWitnesses.Count;
                dependentWitnesses.UnionWith(changedWitnesses);
                if (dependentWitnesses.Count != before)
                {
                    queue.Enqueue(dependent);
                }
            }
        }

        return new FrozenLedgerAdmissionScope(
            witnesses.ToImmutableDictionary(
                static item => item.Key,
                static item => item.Value.ToImmutableHashSet()));

        void Add(RepoPath path, IEnumerable<RepoPath> deltaWitnesses)
        {
            if (!witnesses.TryGetValue(path, out var pathWitnesses))
            {
                pathWitnesses = new HashSet<RepoPath>();
                witnesses.Add(path, pathWitnesses);
            }

            pathWitnesses.UnionWith(deltaWitnesses);
        }
    }

    private static ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> ReverseDependencies(
        IReadOnlyDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency)
    {
        var result = new Dictionary<RepoPath, HashSet<RepoPath>>();
        foreach (var (path, dependencies) in adjacency)
        {
            foreach (var dependency in dependencies)
            {
                if (!result.TryGetValue(dependency, out var dependents))
                {
                    dependents = new HashSet<RepoPath>();
                    result.Add(dependency, dependents);
                }

                dependents.Add(path);
            }
        }

        return result.ToImmutableDictionary(
            static item => item.Key,
            static item => item.Value.ToImmutableHashSet());
    }

    private static ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> BaseReverseDependencies(
        FrozenLedgerBaseView view)
    {
        var pathByIdentity = view.ActiveByPath.Values.ToDictionary(
            static entry => entry.Material.FrozenNodeId,
            static entry => entry.Material.RepoPath);
        var result = new Dictionary<RepoPath, HashSet<RepoPath>>();
        foreach (var entry in view.ActiveByPath.Values)
        {
            foreach (var dependencyIdentity in entry.Material.PrerequisiteFrozenNodeIds)
            {
                if (!pathByIdentity.TryGetValue(dependencyIdentity, out var dependencyPath))
                {
                    continue;
                }

                if (!result.TryGetValue(dependencyPath, out var dependents))
                {
                    dependents = new HashSet<RepoPath>();
                    result.Add(dependencyPath, dependents);
                }

                dependents.Add(entry.Material.RepoPath);
            }
        }

        return result.ToImmutableDictionary(
            static item => item.Key,
            static item => item.Value.ToImmutableHashSet());
    }

    private static IEnumerable<RepoPath> DependentsOf(
        RepoPath path,
        ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> current,
        ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> baseline) =>
        (current.TryGetValue(path, out var currentPaths)
            ? currentPaths
            : ImmutableHashSet<RepoPath>.Empty)
        .Union(baseline.TryGetValue(path, out var basePaths)
            ? basePaths
            : ImmutableHashSet<RepoPath>.Empty);
}

public static partial class FrozenLedger
{
    internal static FrozenLedgerAdmissionFailure? ValidateAdmissionDelta(
        FrozenLedgerAdmissionPreparation preparation,
        FrozenLedgerAdmissionScope scope,
        FrozenMaterialCatalog catalog,
        IFrozenLedgerReplacementAuthorization replacementAuthorization)
    {
        ArgumentNullException.ThrowIfNull(preparation);
        ArgumentNullException.ThrowIfNull(scope);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(replacementAuthorization);
        try
        {
            var replacementAuthorized = preparation.Replacement is { } replacement
                && replacementAuthorization.IsAuthorized(
                    new FrozenLedgerReplacementAuthorizationContext(
                        replacement,
                        preparation.BaseView,
                        catalog));
            var active = replacementAuthorized
                ? new Dictionary<string, FrozenActiveEntry>(StringComparer.Ordinal)
                : preparation.BaseView.ActiveByCase.ToDictionary(
                    static item => item.Key,
                    static item => item.Value,
                    StringComparer.Ordinal);
            var allCaseIds = replacementAuthorized
                ? new HashSet<string>(StringComparer.Ordinal)
                : preparation.BaseView.AllCaseIds.ToHashSet(StringComparer.Ordinal);
            var activePathCases = active.Values.ToDictionary(
                static entry => entry.Material.RepoPath,
                static entry => entry.Payload.CaseId);
            foreach (var item in preparation.DeltaEvents)
            {
                try
                {
                    if (item.SchemaVersion != FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion)
                    {
                        throw new FormatException(
                            $"New accepted event must use schema_version {FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion}.");
                    }

                    if (item.EventType != "Freeze")
                    {
                        throw new FormatException(
                            $"Event type {item.EventType} is not legal in an admission delta.");
                    }

                    var freeze = ParseFreeze(item.Payload, catalog);
                    var freezePath = RepoPath.CreateKnown(freeze.DescriptorSelector);
                    if (!allCaseIds.Add(freeze.CaseId)
                        || activePathCases.ContainsKey(freezePath))
                    {
                        throw new FormatException(
                            "Freeze reused an active case ID or module path.");
                    }

                    var material = catalog.ByPath[freezePath];
                    active.Add(
                        freeze.CaseId,
                        new FrozenActiveEntry(material, freeze, item.EventHash));
                    activePathCases.Add(freezePath, freeze.CaseId);
                }
                catch (Exception exception) when (exception is FormatException
                    or InvalidOperationException
                    or KeyNotFoundException)
                {
                    var affectedPath = item.DescriptorPath;
                    var witnesses = scope.Paths.Contains(affectedPath)
                        ? scope.WitnessesFor(affectedPath)
                        : ImmutableArray.Create(item.SourcePath);
                    return Failure([affectedPath], witnesses, exception.Message);
                }
            }

            var actualByPath = active.Values.ToDictionary(static entry => entry.Material.RepoPath);
            var recordedPathsByIdentity = FrozenPathsByIdentity(
                active.Values.Select(static entry => entry.Material));
            var currentPathsByIdentity = FrozenPathsByIdentity(
                active.Values.Select(static entry => entry.Material),
                catalog.ClosedNodes);
            foreach (var path in scope.Paths.OrderBy(static item => item.Value, StringComparer.Ordinal))
            {
                var hasExpected = catalog.ByPath.TryGetValue(path, out var material);
                var hasActual = actualByPath.TryGetValue(path, out var entry);
                if (hasExpected && !hasActual)
                {
                    return Failure(
                        [path],
                        scope.WitnessesFor(path),
                        $"Closed module {path.Value} is missing a Freeze event; run ledger-append.");
                }

                if (!hasExpected && hasActual)
                {
                    return Failure(
                        [path],
                        scope.WitnessesFor(path),
                        $"Active frozen history contains module {path.Value} outside the current Closed catalog; append Revoke first.");
                }

                if (!hasExpected || !hasActual)
                {
                    continue;
                }

                var activeEntry = entry!;
                var expectedMaterial = material!;
                var materialMatches = FrozenLedgerHistoricalFreezeMatcher.HistoricalActiveFreezeMatches(
                    activeEntry.Payload,
                    expectedMaterial,
                    out var materialDifferences);
                if (materialMatches)
                {
                    continue;
                }

                var differenceMessage = string.Join("; ", materialDifferences);

                if (activeEntry.Payload.StatementId != expectedMaterial.StatementId
                    || !activeEntry.Payload.DeclarationStatementIds.SequenceEqual(
                        expectedMaterial.DeclarationStatementIds))
                {
                    return Failure(
                        [path],
                        scope.WitnessesFor(path),
                        $"Active module {path.Value} statement identity changed; append Revoke first.; field differences: {differenceMessage}");
                }

                return Failure(
                    [path],
                    scope.WitnessesFor(path),
                    $"Active module {path.Value} changed identity; append Revoke before rerunning ledger-append; field differences: {differenceMessage}");
            }

            return null;
        }
        catch (Exception exception) when (exception is FormatException
            or InvalidOperationException
            or KeyNotFoundException)
        {
            throw new InvalidOperationException(
                "trusted protected-base frozen view could not be consumed by incremental admission",
                exception);
        }
    }

    private static FrozenLedgerAdmissionFailure Failure(
        ImmutableArray<RepoPath> affectedPaths,
        ImmutableArray<RepoPath> witnesses,
        string message) => new(
            affectedPaths,
            witnesses,
            message + "; delta witness: "
                + string.Join(", ", witnesses.Select(static item => item.Value)));

}
