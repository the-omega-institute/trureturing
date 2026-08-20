using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record FrozenLedgerAdmissionPreparation(
    FrozenLedgerBaseView BaseView,
    ImmutableArray<DagLedgerFileEvent> DeltaEvents,
    ImmutableHashSet<string> LeanReportProducerPaths,
    TrustedFrozenGitReferences TrustedDeltaReferences,
    FrozenLedgerConsistent? RevocationBaseline = null,
    TrustedRevocationReceiptStore? TrustedRevocationReceipts = null,
    RepositorySnapshot? ProtectedBaseSnapshot = null);

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
                || FrozenLedgerDeltaPredicate.IsDeltaDefinitionInput(change.Path.Value)
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

            if (item.EventType == "Revoke")
            {
                var revoke = FrozenLedger.ReadTrustedRevoke(item.Payload);
                foreach (var caseId in revoke.AffectedCaseIds)
                {
                    if (preparation.BaseView.ActiveByCase.TryGetValue(caseId, out var entry))
                    {
                        Add(entry.Material.RepoPath, [item.SourcePath]);
                    }
                }
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
        RawChangeSet changes,
        TrustedFrozenGitReferences trustedReferences,
        LeanAxiomReport? report = null,
        RepositorySnapshot? snapshot = null)
    {
        ArgumentNullException.ThrowIfNull(preparation);
        ArgumentNullException.ThrowIfNull(scope);
        ArgumentNullException.ThrowIfNull(catalog);
        ArgumentNullException.ThrowIfNull(changes);
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
            var supersededBaseCases = new HashSet<string>(StringComparer.Ordinal);
            foreach (var item in preparation.DeltaEvents)
            {
                try
                {
                    if (item.SchemaVersion != FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion)
                    {
                        throw new FormatException(
                            $"New accepted event must use schema_version {FrozenLedgerCanonicalWriter.CurrentDagSchemaVersion}.");
                    }

                    if (item.EventType == "Freeze")
                    {
                        var freeze = ParseFreeze(
                            item.Payload,
                            catalog,
                            trustedReferences,
                            requireCatalogRevisionIdentity: false);
                        var freezePath = RepoPath.CreateKnown(freeze.Input.DescriptorSelector);
                        if (!allCaseIds.Add(freeze.CaseId)
                            || activePathCases.ContainsKey(freezePath))
                        {
                            throw new FormatException(
                                "Freeze reused a historical case ID or active module path.");
                        }

                        var material = catalog.ByPath[freezePath];
                        active.Add(
                            freeze.CaseId,
                            new FrozenActiveEntry(material, freeze, item.EventHash));
                        activePathCases.Add(freezePath, freeze.CaseId);
                    }
                    else if (item.EventType == "Reattest")
                    {
                        var reattest = ParseReattest(
                            item.Payload,
                            active,
                            trustedReferences,
                            requireAxiomClosure: true);
                        var entry = active[reattest.CaseId];
                        var material = ValidateReattestCandidateMaterial(
                            reattest,
                            entry,
                            catalog,
                            "is not Closed");

                        active[reattest.CaseId] = ApplyReattest(
                            entry,
                            reattest,
                            item.EventHash,
                            material);
                    }
                    else if (item.EventType == SupersedeEventType)
                    {
                        var supersede = ValidateSupersede(
                            item.Payload,
                            active,
                            trustedReferences,
                            catalog,
                            LeanImportClosure.RepositoryClosureIsUnchanged(
                                catalog.Dag,
                                active[FrozenLedgerAttestationChain.RequiredString(
                                    item.Payload,
                                    "case_id")].Material.RepoPath,
                                changes),
                            report is null || snapshot is null
                                || LeanImportClosure.ExternalImportsHaveNamedPinCoverage(
                                    report,
                                    active[FrozenLedgerAttestationChain.RequiredString(
                                        item.Payload,
                                        "case_id")].Material.RepoPath,
                                    snapshot),
                            report is not null
                                && snapshot is not null
                                && preparation.ProtectedBaseSnapshot is not null
                                && LeanImportClosure.RelevantSemanticPinsChanged(
                                    report,
                                    active[FrozenLedgerAttestationChain.RequiredString(
                                        item.Payload,
                                        "case_id")].Material.RepoPath,
                                    active[FrozenLedgerAttestationChain.RequiredString(
                                        item.Payload,
                                        "case_id")],
                                    preparation.ProtectedBaseSnapshot,
                                    snapshot),
                            report is not null
                                && LeanImportClosure.CandidateStatementsAvoidTrivialTruth(
                                    report,
                                    active[FrozenLedgerAttestationChain.RequiredString(
                                        item.Payload,
                                        "case_id")].Material.RepoPath));
                        if (!preparation.BaseView.ActiveByCase.ContainsKey(supersede.CaseId)
                            || !supersededBaseCases.Add(supersede.CaseId))
                        {
                            throw new FormatException(
                                "Supersede must target each protected-base active case exactly once.");
                        }

                        active[supersede.CaseId] = ApplySupersede(
                            active[supersede.CaseId],
                            supersede,
                            item.EventHash);
                    }
                    else if (item.EventType == "Revoke")
                    {
                        var baseline = preparation.RevocationBaseline
                            ?? throw new FormatException("Revoke admission baseline is unavailable.");
                        var receipts = preparation.TrustedRevocationReceipts
                            ?? throw new FormatException("Revoke admission receipt capability is unavailable.");
                        var revoke = ParseRevoke(item.Payload, baseline, active, receipts);
                        foreach (var caseId in revoke.AffectedCaseIds)
                        {
                            var entry = active[caseId];
                            active.Remove(caseId);
                            activePathCases.Remove(entry.Material.RepoPath);
                        }
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
                    var witnesses = scope.Paths.Contains(affectedPath)
                        ? scope.WitnessesFor(affectedPath)
                        : ImmutableArray.Create(item.SourcePath);
                    return Failure([affectedPath], witnesses, exception.Message);
                }
            }

            if (scope.EnvironmentChanged)
            {
                foreach (var baseEntry in preparation.BaseView.ActiveByCase.Values.OrderBy(
                    static entry => entry.Material.RepoPath.Value,
                    StringComparer.Ordinal))
                {
                    if (!supersededBaseCases.Contains(baseEntry.Payload.CaseId))
                    {
                        return Failure(
                            [baseEntry.Material.RepoPath],
                            scope.WitnessesFor(baseEntry.Material.RepoPath),
                            $"Active module {baseEntry.Material.RepoPath.Value} is missing a Supersede event for the environment pin change.");
                    }
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
                var materialMatches = HistoricalActiveFreezeMatches(
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
                    $"Active module {path.Value} has material/blob drift and lacks a matching Reattest event; run ledger-sync.; field differences: {differenceMessage}");
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

    private static bool HistoricalActiveFreezeMatches(
        FrozenFreezePayload payload,
        FrozenNodeMaterial material,
        out ImmutableArray<string> differences)
    {
        var result = ImmutableArray.CreateBuilder<string>();
        if (!payload.DeclarationStatementIds.SequenceEqual(material.DeclarationStatementIds))
        {
            result.Add(SequenceDifference(
                "DeclarationStatementIds",
                material.DeclarationStatementIds,
                payload.DeclarationStatementIds,
                static item =>
                    $"{item.DeclarationNameKey}|{item.Kind}|{item.StatementId.Value}"));
        }

        if (payload.StatementId != material.StatementId)
        {
            result.Add(ScalarDifference(
                "StatementId",
                material.StatementId.Value,
                payload.StatementId.Value));
        }

        if (payload.WitnessId != material.WitnessId)
        {
            result.Add(ScalarDifference(
                "WitnessId",
                material.WitnessId.Value,
                payload.WitnessId.Value));
        }

        if (payload.FrozenNodeId != material.FrozenNodeId)
        {
            result.Add(ScalarDifference(
                "FrozenNodeId",
                material.FrozenNodeId.Value,
                payload.FrozenNodeId.Value));
        }

        if (!payload.PrerequisiteFrozenNodeIds.SequenceEqual(material.PrerequisiteFrozenNodeIds))
        {
            result.Add(SequenceDifference(
                "PrerequisiteFrozenNodeIds",
                material.PrerequisiteFrozenNodeIds,
                payload.PrerequisiteFrozenNodeIds,
                static item => item.Value));
        }

        if (payload.Input.DescriptorBlobOid != material.Attestation.SourceBlobOid)
        {
            result.Add(ScalarDifference(
                "Input.DescriptorBlobOid",
                material.Attestation.SourceBlobOid,
                payload.Input.DescriptorBlobOid));
        }

        if (payload.Input.DescriptorSelector != material.RepoPath.Value)
        {
            result.Add(ScalarDifference(
                "Input.DescriptorSelector",
                material.RepoPath.Value,
                payload.Input.DescriptorSelector));
        }

        differences = result.ToImmutable();
        return differences.IsEmpty;
    }

    private static string ScalarDifference(string field, string expected, string actual) =>
        $"{field} expected={expected}, actual={actual}";

    private static string SequenceDifference<T>(
        string field,
        ImmutableArray<T> expected,
        ImmutableArray<T> actual,
        Func<T, string> format)
    {
        var missing = MissingItems(expected, actual);
        var extra = MissingItems(actual, expected);
        var shape = missing.IsEmpty && extra.IsEmpty
            ? "order differs"
            : $"missing={FormatSequence(missing, format)}, extra={FormatSequence(extra, format)}";
        return $"{field} expected={FormatSequence(expected, format)}, "
            + $"actual={FormatSequence(actual, format)}, {shape}";
    }

    private static ImmutableArray<T> MissingItems<T>(
        ImmutableArray<T> expected,
        ImmutableArray<T> actual)
    {
        var remaining = actual.ToList();
        var missing = ImmutableArray.CreateBuilder<T>();
        foreach (var item in expected)
        {
            var index = remaining.FindIndex(candidate =>
                EqualityComparer<T>.Default.Equals(candidate, item));
            if (index < 0)
            {
                missing.Add(item);
            }
            else
            {
                remaining.RemoveAt(index);
            }
        }

        return missing.ToImmutable();
    }

    private static string FormatSequence<T>(
        ImmutableArray<T> items,
        Func<T, string> format) =>
        "[" + string.Join(", ", items.Select(format)) + "]";
}
