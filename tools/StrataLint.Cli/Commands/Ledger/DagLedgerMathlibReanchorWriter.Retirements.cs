using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DagLedgerMathlibReanchorWriter
{
    private static CommandResult ValidateCompletedUpstreamRetirements(
        RepositorySnapshot protectedBase,
        TruthContext truth,
        FrozenStateCatalog baseState,
        ImmutableHashSet<RepoPath> retired,
        ImmutableArray<RepoPath> retained)
    {
        if (!EffectiveLeanPins.TryRead(protectedBase, out var basePins)
            || !EffectiveLeanPins.TryRead(truth.Snapshot, out var currentPins)
            || basePins!.MathlibRevision == currentPins!.MathlibRevision)
            throw new InvalidOperationException("completed upstream retirement requires a changed adopted mathlib pin");
        foreach (var path in retired)
        {
            if (!protectedBase.Files.ContainsKey(path)
                || !baseState.Records.ContainsKey(path)
                || truth.Snapshot.Files.ContainsKey(path)
                || truth.Snapshot.Files.ContainsKey(FrozenStatePath.FromModulePath(path))
                || truth.Report.Files.ContainsKey(path))
                throw new InvalidOperationException($"upstream port is not a completed paired source/state retirement: {path.Value}");
        }
        var currentState = FrozenStateCatalog.Load(truth.Snapshot);
        if (!retained.ToImmutableHashSet().SetEquals(currentState.Records.Keys))
            throw new InvalidOperationException("completed retirement must retain exactly every other protected-base frozen owner");
        var retiredNames = retired.Select(LeanImportClosure.ModuleName).ToImmutableHashSet(StringComparer.Ordinal);
        if (truth.Report.Files.Values.Any(report => report.Imports.Any(retiredNames.Contains))
            || truth.Snapshot.Files.Values.Where(file => LeanClosureValidator.IsReportLean(file.Path.Value))
                .Any(file => LeanSourceCatalog.ParseFileImports(file).Any(retiredNames.Contains)))
            throw new InvalidOperationException("current source or report still imports an already-retired upstream port");
        var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
        var drift = ImmutableHashSet.CreateBuilder<RepoPath>();
        foreach (var path in retained)
        {
            if (!truth.Report.Files.TryGetValue(path, out var report)
                || !states.TryGetValue(path, out var status) || status is not TruthState.Closed)
                throw new InvalidOperationException("canonical Lean report cannot materialize retained Closed module: " + path.Value);
            var planned = FrozenStateRecord.FromReport(path, report);
            if (currentState.Records[path].StatementId != planned.StatementId
                || !currentState.Records[path].Declarations.SequenceEqual(planned.Declarations))
                throw new InvalidOperationException("completed retirement frozen state does not match the current report: " + path.Value);
            if (baseState.Records[path].StatementId != planned.StatementId
                || !baseState.Records[path].Declarations.SequenceEqual(planned.Declarations))
                drift.Add(path);
        }
        var retiredStatePaths = retired.Select(FrozenStatePath.FromModulePath).ToImmutableHashSet();
        var retainedBaseState = FrozenStateCatalog.Load(RepositorySnapshot.Create(protectedBase.Files
            .Where(pair => !retiredStatePaths.Contains(pair.Key)).ToImmutableDictionary()));
        var comparison = retained.ToImmutableHashSet();
        var failures = MathlibUpgradePropositionSourceDiagnostics.FindFailures(
            protectedBase, truth.Snapshot, comparison, retainedBaseState, truth.Report);
        var authorized = new MathlibUpgradeFrozenLedgerReplacementAuthorization(protectedBase, truth.Snapshot)
            .IsAuthorized(comparison, retainedBaseState, truth.Report);
        var output = $"MATHLIB_REANCHOR recognition=completed-canonical-publication retired_upstream_ports={retired.Count} published_modules=0\n"
            + $"MATHLIB_REANCHOR validated_retained_modules={retained.Length}\n"
            + $"MATHLIB_REANCHOR drift_seed_modules={drift.Count}\n"
            + $"AUTHORIZATION proposition_source_equivalent={(failures.IsEmpty ? "pass" : "fail")} failed_modules={failures.Length}\n"
            + $"AUTHORIZATION overall={(authorized ? "pass" : "fail")}\n"
            + string.Concat(failures.Select(static path => $"PROPOSITION_SOURCE_FAILURE {path.Value}\n"));
        return new(authorized, output, authorized ? string.Empty
            : "MATHLIB_REANCHOR_FAILED completed publication authorization failed; frozen state was not published\n");
    }
}
