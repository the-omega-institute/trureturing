using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DagLedgerMathlibReanchorWriter
{
    private static CommandResult ValidateCompletedUpstreamRetirements(
        RepositorySnapshot protectedBase,
        RepositorySnapshot current,
        AcceptedLeanClosure lean,
        FrozenLedgerBaseView baseView,
        FrozenMaterialCatalog completeCatalog,
        ImmutableDictionary<RepoPath, TruthState> states,
        ImmutableDictionary<RepoPath, ImmutableArray<RepoPath>> adjacency,
        ImmutableArray<RepositoryFile> currentLedgerFiles,
        ImmutableHashSet<RepoPath> retired,
        ImmutableArray<RepoPath> driftPaths)
    {
        // This path validates a completed canonical publication. It never retires
        // a module, deletes state, or turns an absent report row into authorization.
        if (!EffectiveLeanPins.TryRead(protectedBase, out var basePins)
            || !EffectiveLeanPins.TryRead(current, out var currentPins)
            || basePins!.MathlibRevision == currentPins!.MathlibRevision)
            throw new InvalidOperationException("completed upstream retirement requires a changed adopted mathlib pin");
        if (FrozenAcceptedEventLoader.LoadFiles(currentLedgerFiles) is DagLedgerFilesLoadOutcome.Invalid invalid)
            throw new InvalidOperationException("completed retirement accepted events are invalid: " + invalid.Message);
        var currentView = FrozenLedgerBaseViewReader.Read(RepositorySnapshot.Create(
            currentLedgerFiles.ToImmutableDictionary(static file => file.Path)));
        foreach (var path in retired)
        {
            if (!path.Value.StartsWith("D5/", StringComparison.Ordinal)
                || !protectedBase.Files.ContainsKey(path)
                || !baseView.ActiveByPath.ContainsKey(path)
                || current.Files.ContainsKey(path)
                || current.Files.ContainsKey(FrozenStatePath.FromModulePath(path))
                || currentView.ActiveByPath.ContainsKey(path)
                || completeCatalog.ByPath.ContainsKey(path))
                throw new InvalidOperationException($"upstream port is not a completed paired retirement of the protected-base owner: {path.Value}");
        }
        var retained = baseView.ActiveByPath.Keys.Except(retired).ToImmutableHashSet();
        if (!retained.SetEquals(currentView.ActiveByPath.Keys))
            throw new InvalidOperationException("completed retirement must retain exactly every other protected-base frozen owner");
        if (!retained.SetEquals(FrozenStateCatalog.Load(current).Records.Keys))
            throw new InvalidOperationException("completed retirement must retain exactly the paired frozen-state owners");
        foreach (var report in lean.Report.Files.Values)
        {
            if (report.Imports.Any(import => retired.Any(path => LeanImportClosure.ModuleName(path) == import)))
                throw new InvalidOperationException("current report still imports an already-retired upstream port");
        }
        var currentCatalog = FrozenContentAddress.BuildAdmissionCatalog(
            current, lean, states, adjacency, retained, currentView.ActiveByPath);
        var alignment = FrozenLedger.ValidateTrustedHistory(currentView, currentCatalog, requireCompleteCatalog: false);
        if (alignment is FrozenLedgerValidationOutcome.Rejected rejected)
            throw new InvalidOperationException("completed retirement frozen alignment failed: " + rejected.Message);
        foreach (var path in retained)
        {
            if (!current.Files.TryGetValue(FrozenStatePath.FromModulePath(path), out var stateFile)
                || FrozenStateRecordLoader.Load(stateFile).StatementId != currentCatalog.ByPath[path].StatementId)
                throw new InvalidOperationException($"completed retirement state/event statement_id conflict: {path.Value}");
        }
        var changed = driftPaths.Except(retired).ToImmutableHashSet();
        var propositionFailures = MathlibUpgradePropositionSourceDiagnostics.FindFailures(
            protectedBase, current, changed, baseView, currentCatalog);
        var closureFailures = retained.Except(changed).Where(path =>
            !baseView.ActiveByPath[path].Material.DeclarationStatementIds.SequenceEqual(
                currentCatalog.ByPath[path].DeclarationStatementIds)).ToImmutableArray();
        var axiomFailures = retained.Where(path => currentCatalog.ByPath[path].AxiomClosure
            .Any(axiom => !LeanAxiomFacts.IsStandard(axiom))).ToImmutableArray();
        var authorized = propositionFailures.IsEmpty && closureFailures.IsEmpty && axiomFailures.IsEmpty;
        var output = RenderResult(driftPaths.Except(retired).ToImmutableArray(), [],
            true, propositionFailures, closureFailures, axiomFailures, authorized)
            .Replace("AUTHORIZATION incremental_replacement=pass", "AUTHORIZATION completed_publication=pass", StringComparison.Ordinal)
            + $"MATHLIB_REANCHOR recognition=completed-canonical-publication retired_upstream_ports={retired.Count} "
            + $"retained_descendants={FrozenLedgerReplacementClosure.DescendantsFrom(baseView, retired).Except(retired).Count()} published_modules=0\n"
            + $"MATHLIB_REANCHOR validated_retained_modules={retained.Count}\n";
        return new CommandResult(authorized, output,
            authorized ? string.Empty : "MATHLIB_REANCHOR_FAILED completed publication authorization failed\n");
    }

}
