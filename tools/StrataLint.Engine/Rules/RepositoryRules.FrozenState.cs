using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class RepositoryRules
{
    private static ImmutableArray<RuleFinding> FrozenStates(RuleEvaluationContext context)
    {
        var affected = AffectedFrozenStateFiles(context);
        if (affected.IsEmpty)
        {
            return [];
        }

        var findings = ImmutableArray.CreateBuilder<RuleFinding>();
        var states = LeanTruthStates.Resolve(context.Current, context.Lean);
        var acceptedByPath = AcceptedFreezePins(context, affected, findings);
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

            if (acceptedByPath.TryGetValue(modulePath, out var acceptedPins))
            {
                foreach (var accepted in acceptedPins.Where(pin => pin != record.StatementId))
                {
                    findings.Add(new RuleFinding(
                        displayPath,
                        $"selector {modulePath.Value} Freeze/state mismatch: "
                        + $"accepted={accepted.Value} state={record.StatementId.Value}"));
                }
            }
        }

        return findings.ToImmutable();
    }

    private static ImmutableArray<RepositoryFile> AffectedFrozenStateFiles(
        RuleEvaluationContext context)
    {
        if (context.RuleImplementationChanged)
        {
            return context.Current.Files.Values
                .Where(static file => FrozenStatePath.IsUnderRoot(file.Path.Value))
                .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
                .ToImmutableArray();
        }

        var paths = context.Changes.Paths
            .Where(path => FrozenStatePath.IsUnderRoot(path.Value)
                && context.Current.Files.ContainsKey(path))
            .ToHashSet();
        foreach (var modulePath in context.Changes.Paths.Where(
            FrozenStatePath.IsCanonicalModulePath))
        {
            try
            {
                var statePath = FrozenStatePath.FromModulePath(modulePath);
                if (context.Current.Files.ContainsKey(statePath))
                {
                    paths.Add(statePath);
                }
            }
            catch (ArgumentException)
            {
            }
        }

        return paths
            .OrderBy(static path => path.Value, StringComparer.Ordinal)
            .Select(path => context.Current.Files[path])
            .ToImmutableArray();
    }

    private static ImmutableDictionary<RepoPath, ImmutableArray<StatementId>> AcceptedFreezePins(
        RuleEvaluationContext context,
        ImmutableArray<RepositoryFile> affected,
        ImmutableArray<RuleFinding>.Builder findings)
    {
        var acceptedFiles = context.Current.Files.Values
            .Where(static file => FrozenLedgerChangeClassifier.IsAcceptedEventPath(file.Path.Value))
            .ToImmutableArray();
        var load = FrozenAcceptedEventLoader.LoadFiles(acceptedFiles);
        if (load is DagLedgerFilesLoadOutcome.Invalid invalid)
        {
            foreach (var file in affected)
            {
                findings.Add(new RuleFinding(
                    "frozen state " + file.Path.Value,
                    "accepted Freeze events cannot be read for C6: " + invalid.Message));
            }

            return ImmutableDictionary<RepoPath, ImmutableArray<StatementId>>.Empty;
        }

        var events = ((DagLedgerFilesLoadOutcome.Loaded)load).Events;
        return events
            .Where(static item => item.EventType == "Freeze")
            .GroupBy(static item => item.DescriptorPath)
            .ToImmutableDictionary(
                static group => group.Key,
                static group => group
                    .Select(item => StatementId.Create(
                        item.Payload.GetProperty("statement_id").GetString()
                        ?? throw new FormatException("Freeze statement_id is null.")))
                    .ToImmutableArray());
    }
}
