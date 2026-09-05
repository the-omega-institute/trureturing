using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> FrozenStates(RuleEvaluationContext context)
    {
        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        ValidateChangedAcceptedFreezePins(context, findings);

        var affected = AffectedFrozenStateFiles(context);
        if (affected.IsEmpty)
        {
            return findings.ToImmutable();
        }

        var states = LeanTruthStates.Resolve(context.Current, context.Lean);
        foreach (var file in affected)
        {
            var displayPath = "frozen state " + file.Path.Value;
            if (!FrozenStatePath.TryToModulePath(file.Path.Value, out var modulePath))
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    "path must encode exactly one canonical repository Lean module"));
                continue;
            }

            FrozenStateRecord record;
            try
            {
                record = FrozenStateRecordLoader.Load(file);
            }
            catch (FormatException exception)
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    exception.InnerException?.Message ?? exception.Message));
                continue;
            }

            ObservePinChange(context, file, modulePath, record, findings);

            if (!context.Current.Files.ContainsKey(modulePath))
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"module {modulePath.Value} does not exist"));
                continue;
            }

            if (!states.TryGetValue(modulePath, out var state) || state is not TruthState.Closed)
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"module {modulePath.Value} has TruthState={state}, expected Closed"));
                continue;
            }

            if (!context.Lean.Report.Files.TryGetValue(modulePath, out var report))
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"module {modulePath.Value} has no current Lean report"));
                continue;
            }

            var actual = FrozenContentAddress.ComputeModuleStatementId(modulePath, report);
            if (record.StatementId != actual)
            {
                findings.Add(new RuleFinding(
                    displayPath,
                    $"selector {modulePath.Value} pin mismatch: "
                    + $"stored={record.StatementId.Value} actual={actual.Value}"));
            }
        }

        return findings.ToImmutable();
    }

    // Transitional contract: remove this check together with the accepted directory (#4687).
    // Frozen state remains authoritative; only changed candidate accepted files are read here.
    private static void ValidateChangedAcceptedFreezePins(
        RuleEvaluationContext context,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        foreach (var change in context.Changes.Entries
            .Where(static change =>
                change.Kind is RawChangeKind.Added or RawChangeKind.Modified
                && FrozenLedgerChangeClassifier.IsAcceptedEventPath(change.Path.Value))
            .OrderBy(static change => change.Path.Value, StringComparer.Ordinal))
        {
            if (!context.Current.Files.TryGetValue(change.Path, out var file))
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    "changed accepted event is absent from the candidate snapshot"));
                continue;
            }

            if (TryReadAcceptedEventType(file, out var eventType)
                && eventType != "Freeze")
            {
                continue;
            }

            var load = FrozenAcceptedEventLoader.LoadFiles([file]);
            if (load is DagLedgerFilesLoadOutcome.Invalid invalid)
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    $"accepted event could not be loaded: {invalid.Message}"));
                continue;
            }

            var accepted = ((DagLedgerFilesLoadOutcome.Loaded)load).Events.Single();
            if (accepted.EventType != "Freeze")
            {
                continue;
            }

            var modulePath = accepted.DescriptorPath;
            var statePath = FrozenStatePath.FromModulePath(modulePath);
            if (!context.Current.Files.TryGetValue(statePath, out var stateFile))
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    $"Freeze event for {modulePath.Value} has no frozen-state pin {statePath.Value}; "
                    + "run ledger-align --from-accepted (lane tools predate L3b dual-write)"));
                continue;
            }

            FrozenStateRecord state;
            try
            {
                state = FrozenStateRecordLoader.Load(stateFile);
            }
            catch (FormatException exception)
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    $"Freeze event for {modulePath.Value} has invalid frozen-state pin "
                    + $"{statePath.Value}: {exception.InnerException?.Message ?? exception.Message}"));
                continue;
            }

            var eventPin = StatementId.Create(
                accepted.Payload.GetProperty("statement_id").GetString()!);
            if (state.StatementId != eventPin)
            {
                findings.Add(new RuleFinding(
                    change.Path.Value,
                    $"Freeze event pin mismatch: selector={modulePath.Value} "
                    + $"event pin={eventPin.Value} state pin={state.StatementId.Value}"));
            }
        }
    }

    private static bool TryReadAcceptedEventType(
        RepositoryFile file,
        out string eventType)
    {
        eventType = string.Empty;
        try
        {
            using var document = JsonDocument.Parse(file.RawBytes.AsSpan().ToArray());
            if (document.RootElement.ValueKind is JsonValueKind.Object
                && document.RootElement.TryGetProperty("event_type", out var eventTypeValue)
                && eventTypeValue.ValueKind is JsonValueKind.String
                && eventTypeValue.GetString() is { } value)
            {
                eventType = value;
                return true;
            }
        }
        catch (JsonException)
        {
        }

        return false;
    }

    private static ImmutableArray<RepositoryFile> AffectedFrozenStateFiles(
        RuleEvaluationContext context)
    {
        if (AllFrozenStatesAffected(context))
        {
            return AllCurrentFrozenStateFiles(context);
        }

        var paths = context.Changes.Paths
            .Where(path => FrozenStatePath.IsUnderRoot(path.Value)
                && context.Current.Files.ContainsKey(path))
            .ToHashSet();
        var changedModules = context.Changes.Paths
            .Where(FrozenStatePath.IsCanonicalModulePath)
            .ToImmutableHashSet();
        if (!changedModules.IsEmpty)
        {
            var currentAdjacency = LeanImportAdjacency.Build(context.Current, context.Lean);
            // RuleEvaluationContext has no baseline report, only the baseline source snapshot.
            // CLAUDE.md rule 19 keeps base at SHA/object-diff level without checkout or compilation.
            var baselineAdjacency = LeanImportAdjacency.BuildFromSources(context.Baseline);
            var currentDependents = ReverseDependencies(currentAdjacency);
            var baselineDependents = ReverseDependencies(baselineAdjacency);
            var affectedModules = changedModules.ToHashSet();
            var pending = new Queue<RepoPath>(changedModules);
            while (pending.TryDequeue(out var changed))
            {
                foreach (var dependent in DependentsOf(
                    changed,
                    currentDependents,
                    baselineDependents))
                {
                    if (affectedModules.Add(dependent))
                    {
                        pending.Enqueue(dependent);
                    }
                }
            }

            foreach (var modulePath in affectedModules)
            {
                var statePath = FrozenStatePath.FromModulePath(modulePath);
                if (context.Current.Files.ContainsKey(statePath))
                {
                    paths.Add(statePath);
                }
            }
        }

        return paths
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => context.Current.Files[path])
            .ToImmutableArray();
    }

    private static bool AllFrozenStatesAffected(RuleEvaluationContext context) =>
        context.RuleImplementationChanged
        || Changed(context, IsLeanReportProducerInput);

    private static ImmutableArray<RepositoryFile> AllCurrentFrozenStateFiles(
        RuleEvaluationContext context) =>
        context.Current.Files.Values
            .Where(static file => FrozenStatePath.IsUnderRoot(file.Path.Value))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToImmutableArray();

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

    private static IEnumerable<RepoPath> DependentsOf(
        RepoPath path,
        IReadOnlyDictionary<RepoPath, ImmutableHashSet<RepoPath>> current,
        IReadOnlyDictionary<RepoPath, ImmutableHashSet<RepoPath>> baseline) =>
        (current.TryGetValue(path, out var currentPaths)
            ? currentPaths
            : ImmutableHashSet<RepoPath>.Empty)
        .Union(baseline.TryGetValue(path, out var baselinePaths)
            ? baselinePaths
            : ImmutableHashSet<RepoPath>.Empty);

    private static void ObservePinChange(
        RuleEvaluationContext context,
        RepositoryFile currentFile,
        RepoPath modulePath,
        FrozenStateRecord currentRecord,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        if (!context.Baseline.Files.TryGetValue(currentFile.Path, out var baselineFile))
        {
            return;
        }

        try
        {
            var baselineRecord = FrozenStateRecordLoader.Load(baselineFile);
            if (baselineRecord.StatementId != currentRecord.StatementId)
            {
                findings.Add(new RuleFinding(
                    "frozen state " + currentFile.Path.Value,
                    $"FROZEN_PIN_CHANGE selector={modulePath.Value} "
                    + $"old={baselineRecord.StatementId.Value} new={currentRecord.StatementId.Value}",
                    AdmissionEffect.Observe));
            }
        }
        catch (FormatException)
        {
            // SL-008 judges only the candidate state; an unreadable old record cannot block it.
        }
    }
}
