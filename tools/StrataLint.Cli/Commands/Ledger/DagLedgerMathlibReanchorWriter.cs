using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerMathlibReanchorWriter
{
    internal static CommandResult Reanchor(string root, IRepositoryGateway repository,
        ILeanReportSource source, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--base" || string.IsNullOrWhiteSpace(arguments[1]))
                throw new InvalidOperationException("USAGE: StrataLint ledger-reanchor-mathlib --base REV");
            var protectedBase = Decode(DagLedgerCommandPreparation.Ask(() =>
                repository.ReadRevisionProjection(arguments[1], TruthExportCommand.IsTruthInput)));
            var state = FrozenStateCatalog.Load(protectedBase);
            if (state.Records.IsEmpty) return new(true, "MATHLIB_REANCHOR replacement_modules=0 drift_seed_modules=0 recognition=not-required\n", string.Empty);
            var truth = DagLedgerCommandPreparation.BuildTruthScoped(repository, source, state.Selectors);
            var states = LeanTruthStates.Resolve(truth.Snapshot, truth.Lean);
            var planned = state.Selectors.ToDictionary(static path => path, path =>
                truth.Report.Files.TryGetValue(path, out var module) && states.TryGetValue(path, out var status) && status is TruthState.Closed
                    ? FrozenStateRecord.FromReport(path, module)
                    : throw new InvalidOperationException("canonical Lean report cannot materialize active Closed module: " + path.Value));
            var drift = state.Selectors.Where(path => state.Records[path].StatementId != planned[path].StatementId
                || !state.Records[path].Declarations.SequenceEqual(planned[path].Declarations)).ToImmutableHashSet();
            if (drift.IsEmpty) return new(true, "MATHLIB_REANCHOR replacement_modules=0 drift_seed_modules=0 recognition=not-required\n", string.Empty);
            var failures = MathlibUpgradePropositionSourceDiagnostics.FindFailures(protectedBase, truth.Snapshot, drift, state, truth.Report);
            var authorized = new MathlibUpgradeFrozenLedgerReplacementAuthorization(protectedBase, truth.Snapshot)
                .IsAuthorized(drift, state, truth.Report);
            var output = $"MATHLIB_REANCHOR replacement_modules={drift.Count}\nMATHLIB_REANCHOR drift_seed_modules={drift.Count}\n"
                + $"AUTHORIZATION proposition_source_equivalent={(failures.IsEmpty ? "pass" : "fail")} failed_modules={failures.Length}\n"
                + $"AUTHORIZATION overall={(authorized ? "pass" : "fail")}\n"
                + string.Concat(failures.Select(static path => $"PROPOSITION_SOURCE_FAILURE {path.Value}\n"));
            if (!authorized) return new(false, output, "MATHLIB_REANCHOR_FAILED authorization failed; frozen state was not published\n");
            var backups = drift.ToDictionary(static path => path, path => FrozenStateWriter.ReadCurrentBytes(root, path));
            try
            {
                foreach (var path in drift.OrderBy(static path => path.Value, StringComparer.Ordinal))
                    _ = FrozenStateWriter.Write(root, path, planned[path].StatementId, planned[path].Declarations);
            }
            catch
            {
                foreach (var (path, bytes) in backups) FrozenStateWriter.Restore(root, path, bytes);
                throw;
            }
            return new(true, output, string.Empty);
        }
        catch (Exception exception) when (exception is ArgumentException or FormatException or IOException
            or InvalidOperationException or UnauthorizedAccessException
            or DagLedgerCommandPreparation.LeanReportUnusableException or DagLedgerCommandPreparation.RepositoryUnavailableException)
        {
            return new(false, string.Empty, "MATHLIB_REANCHOR_FAILED " + exception.Message
                + (exception.InnerException is null ? string.Empty : " Cause: " + exception.InnerException.Message) + "\n");
        }
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
    };
}
