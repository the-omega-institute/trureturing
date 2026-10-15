using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class DagLedgerMathlibReanchorWriter
{
    internal static CommandResult Reanchor(string root, IRepositoryGateway repository,
        ILeanReportSource source, IReadOnlyList<string> arguments)
    {
        try
        {
            var options = ParseArguments(arguments);
            var protectedBase = Decode(DagLedgerCommandPreparation.Ask(() =>
                repository.ReadRevisionProjection(options.ProtectedBase, TruthExportCommand.IsTruthInput)));
            var state = FrozenStateCatalog.Load(protectedBase);
            if (options.Retired.Any(path => !state.Records.ContainsKey(path)))
                throw new InvalidOperationException("retired upstream port must be a protected-base frozen member");
            if (state.Records.IsEmpty) return new(true, "MATHLIB_REANCHOR replacement_modules=0 drift_seed_modules=0 recognition=not-required\n", string.Empty);
            var retained = state.Selectors.Where(path => !options.Retired.Contains(path)).ToImmutableArray();
            var truth = retained.IsEmpty
                ? DagLedgerCommandPreparation.BuildTruth(repository, source)
                : DagLedgerCommandPreparation.BuildTruthScoped(repository, source, retained);
            if (!options.Retired.IsEmpty)
                return ValidateCompletedUpstreamRetirements(protectedBase, truth, state, options.Retired, retained);
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

    private static ReanchorOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count < 2 || arguments[0] != "--base" || string.IsNullOrWhiteSpace(arguments[1]))
            throw new InvalidOperationException("USAGE: StrataLint ledger-reanchor-mathlib --base REV [--retired-upstream-port MODULE ...]");
        var retired = ImmutableHashSet.CreateBuilder<RepoPath>();
        for (var index = 2; index < arguments.Count; index += 2)
        {
            if (arguments[index] != "--retired-upstream-port" || index + 1 >= arguments.Count
                || !RepoPath.TryCreate(arguments[index + 1], out var path)
                || !path.Value.StartsWith("D5/", StringComparison.Ordinal))
                throw new InvalidOperationException("retired upstream port must name a canonical D5 module");
            _ = FrozenStatePath.FromModulePath(path);
            if (!retired.Add(path)) throw new InvalidOperationException("duplicate retired upstream port");
        }
        return new(arguments[1], retired.ToImmutable());
    }

    private sealed record ReanchorOptions(string ProtectedBase, ImmutableHashSet<RepoPath> Retired);

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) => SnapshotDecoder.Decode(raw) switch
    {
        SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
        SnapshotDecodeOutcome.InfrastructureFailure failure => throw new InvalidOperationException(failure.Message),
    };
}
