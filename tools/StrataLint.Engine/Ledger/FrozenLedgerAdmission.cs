using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record FrozenLedgerAdmissionPreparation(
    FrozenLedgerBaseView BaseView,
    ImmutableArray<DagLedgerFileEvent> DeltaEvents,
    ImmutableHashSet<string> LeanReportProducerPaths,
    TrustedFrozenGitReferences TrustedDeltaReferences);

internal sealed record FrozenLedgerAdmissionFailure(
    ImmutableArray<RepoPath> AffectedPaths,
    ImmutableArray<RepoPath> DeltaWitnessPaths,
    string Message);

internal sealed class FrozenLedgerAdmissionScope
{
    private FrozenLedgerAdmissionScope(
        ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> witnessesByPath,
        bool environmentChanged)
    {
        WitnessesByPath = witnessesByPath;
        EnvironmentChanged = environmentChanged;
    }

    internal ImmutableDictionary<RepoPath, ImmutableHashSet<RepoPath>> WitnessesByPath { get; }

    internal ImmutableHashSet<RepoPath> Paths => WitnessesByPath.Keys.ToImmutableHashSet();

    internal bool EnvironmentChanged { get; }

    internal ImmutableArray<RepoPath> WitnessesFor(RepoPath path) =>
        WitnessesByPath.TryGetValue(path, out var witnesses)
            ? witnesses.OrderBy(static item => item.Value, StringComparer.Ordinal).ToImmutableArray()
            : throw new InvalidOperationException(
                $"frozen-ledger admission scope lost the delta witness for {path.Value}");

    internal static FrozenLedgerAdmissionScope Create(
        RawChangeSet changes,
        FrozenLedgerAdmissionPreparation preparation,
        AcyclicTruthDag currentDag)
    {
        ArgumentNullException.ThrowIfNull(changes);
        ArgumentNullException.ThrowIfNull(preparation);
        ArgumentNullException.ThrowIfNull(currentDag);
        var witnesses = new Dictionary<RepoPath, HashSet<RepoPath>>();
        var environmentChanges = changes.Entries
            .Where(static change => FrozenLedgerDeltaPredicate.IsEnvironmentInput(change.Path.Value))
            .Select(static change => change.Path)
            .ToImmutableArray();
        var allChanges = changes.Entries
            .Where(change => environmentChanges.Contains(change.Path)
                || change.Path.Value == "Trureturing.lean"
                || preparation.LeanReportProducerPaths.Contains(change.Path.Value))
            .Select(static change => change.Path)
            .ToImmutableHashSet();
        var currentClosed = currentDag.Nodes
            .Where(static node => node.State is TruthState.Closed && node.ModuleName is not null)
            .Select(static node => node.RepoPath)
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
            if (item.Input is { } input && RepoPath.TryCreate(input.DescriptorSelector, out var path))
            {
                Add(path, [item.SourcePath]);
            }
        }

        var currentDependents = ReverseDependencies(currentDag);
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
                static item => item.Value.ToImmutableHashSet()),
            !environmentChanges.IsEmpty);

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
        AcyclicTruthDag dag)
    {
        var result = new Dictionary<RepoPath, HashSet<RepoPath>>();
        foreach (var node in dag.Nodes)
        {
            foreach (var dependency in dag.DependenciesOf(node.RepoPath))
            {
                if (!result.TryGetValue(dependency, out var dependents))
                {
                    dependents = new HashSet<RepoPath>();
                    result.Add(dependency, dependents);
                }

                dependents.Add(node.RepoPath);
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
        TrustedFrozenGitReferences trustedReferences)
    {
        ArgumentNullException.ThrowIfNull(preparation);
        ArgumentNullException.ThrowIfNull(scope);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(trustedReferences);
        try
        {
            var active = preparation.BaseView.ActiveByCase.ToDictionary(
                static item => item.Key,
                static item => item.Value,
                StringComparer.Ordinal);
            var allCaseIds = preparation.BaseView.AllCaseIds.ToHashSet(StringComparer.Ordinal);
            var activePathCases = active.Values.ToDictionary(
                static entry => entry.Material.RepoPath,
                static entry => entry.Payload.CaseId);
            foreach (var item in preparation.DeltaEvents)
            {
                try
                {
                    if (item.EventType == "Freeze")
                    {
                        var freeze = ParseFreeze(item.Payload, catalog, trustedReferences);
                        if (!allCaseIds.Add(freeze.CaseId)
                            || activePathCases.ContainsKey(freeze.NodePath))
                        {
                            throw new FormatException(
                                "Freeze reused a historical case ID or active module path.");
                        }

                        var material = catalog.ByPath[freeze.NodePath];
                        active.Add(
                            freeze.CaseId,
                            new FrozenActiveEntry(material, freeze, item.EventHash));
                        activePathCases.Add(freeze.NodePath, freeze.CaseId);
                    }
                    else if (item.EventType == "Reattest")
                    {
                        var reattest = ParseReattest(item.Payload, active, trustedReferences);
                        var entry = active[reattest.CaseId];
                        FrozenNodeMaterial? material = null;
                        if (!reattest.IsLegacyFormat)
                        {
                            if (!catalog.ByPath.TryGetValue(
                                entry.Material.RepoPath,
                                out var candidateMaterial))
                            {
                                throw new FormatException(
                                    $"Reattest target {entry.Material.RepoPath.Value} is not Closed.");
                            }

                            ValidateReattestMaterial(reattest, candidateMaterial);
                            material = candidateMaterial;
                        }

                        active[reattest.CaseId] = ApplyReattest(
                            entry,
                            reattest,
                            item.EventHash,
                            material);
                    }
                    else if (item.EventType == EnvironmentRecoordinateEventType)
                    {
                        var recoordinate = ValidateEnvironmentRecoordinate(
                            item.Payload,
                            active,
                            trustedReferences,
                            catalog);
                        active[recoordinate.CaseId] = ApplyEnvironmentRecoordinate(
                            active[recoordinate.CaseId],
                            recoordinate,
                            item.EventHash);
                    }
                    else if (item.EventType == "Revoke")
                    {
                        throw new FormatException(
                            "incremental admission does not support Revoke; writer-side full validation is required");
                    }
                    else
                    {
                        throw new FormatException(
                            $"Event type {item.EventType} is not legal in an admission delta.");
                    }
                }
                catch (Exception exception) when (exception is FormatException
                    or InvalidOperationException
                    or KeyNotFoundException)
                {
                    var affectedPath = item.Input is { } input
                        && RepoPath.TryCreate(input.DescriptorSelector, out var parsedPath)
                            ? parsedPath
                            : item.SourcePath;
                    return Failure([affectedPath], [item.SourcePath], exception.Message);
                }
            }

            var actualByPath = active.Values.ToDictionary(static entry => entry.Material.RepoPath);
            foreach (var path in scope.Paths.OrderBy(static item => item.Value, StringComparer.Ordinal))
            {
                var hasExpected = catalog.ByPath.TryGetValue(path, out var material);
                var hasActual = actualByPath.TryGetValue(path, out var entry);
                if (hasExpected && !hasActual)
                {
                    return Failure(
                        [path],
                        scope.WitnessesFor(path),
                        $"Closed module {path.Value} is missing a Freeze event; run ledger-sync.");
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
                var materialMatches = HistoricalActiveFreezeMatches(activeEntry.Payload, expectedMaterial);
                var environmentMatches = activeEntry.Environment is null
                    || EnvironmentMatches(activeEntry.Environment, catalog.Environment);
                if (materialMatches && environmentMatches)
                {
                    continue;
                }

                if (activeEntry.Payload.StatementId != expectedMaterial.StatementId
                    || !activeEntry.Payload.DeclarationStatementIds.SequenceEqual(
                        expectedMaterial.DeclarationStatementIds))
                {
                    return Failure(
                        [path],
                        scope.WitnessesFor(path),
                        $"Active module {path.Value} statement identity changed; append Revoke first.");
                }

                if (!environmentMatches)
                {
                    return Failure(
                        [path],
                        scope.WitnessesFor(path),
                        $"Active module {path.Value} environment pins changed; an accepted EnvironmentRecoordinate event is required.");
                }

                return Failure(
                    [path],
                    scope.WitnessesFor(path),
                    $"Active module {path.Value} has material/blob drift and lacks a matching Reattest event; run ledger-sync.");
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
