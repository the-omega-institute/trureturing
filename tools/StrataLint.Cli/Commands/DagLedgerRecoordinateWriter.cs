using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerRecoordinateWriter
{
    internal static CommandResult Recoordinate(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 6
                || arguments[0] != "--old-environment"
                || arguments[2] != "--old-lean-report"
                || arguments[4] != "--candidate-lean-report")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-recoordinate --old-environment COMMIT "
                    + "--old-lean-report FILE --candidate-lean-report FILE");
            }

            var context = DagLedgerCommandPreparation.PrepareRecoordinate(
                repositoryRoot,
                repository,
                arguments[1],
                arguments[3],
                arguments[5]);
            var generation = FrozenLedgerGenerator.AppendEnvironmentRecoordinates(
                context.Baseline,
                context.Catalog,
                context.CandidateReport,
                context.CandidateSnapshot,
                context.OldReport,
                context.OldSnapshot,
                context.OldEnvironment);
            if (generation.ReattestPaths.Length > 0)
            {
                return new CommandResult(
                    true,
                    $"LEDGER_RECOORDINATE deferred_recoordinates={generation.RecoordinatedPaths.Length} "
                    + $"requires_reattest={generation.ReattestPaths.Length} "
                    + $"events={context.Baseline.Events.Length} head={context.Baseline.HeadHash}\n"
                    + RenderReattestPaths(generation.ReattestPaths),
                    string.Empty);
            }

            if (generation.Bytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                return new CommandResult(
                    true,
                    $"LEDGER_RECOORDINATE no environment coordinate drift "
                    + $"requires_reattest={generation.ReattestPaths.Length} "
                    + $"events={context.Baseline.Events.Length} head={context.Baseline.HeadHash}\n",
                    string.Empty);
            }

            var candidateSyntax = DagLedgerCommandPreparation.LoadLedger(
                generation.Bytes.AsSpan(),
                "generated frozen ledger");
            var candidateReferences = DagLedgerCommandPreparation.ScanReferences(
                candidateSyntax,
                "generated frozen ledger");
            var trustedCandidateReferences = repository.ValidateFrozenReferences(candidateReferences);
            var candidate = FrozenLedger.ValidateCandidate(
                candidateSyntax,
                context.Baseline,
                context.Catalog,
                trustedCandidateReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            if (!DagLedgerCommandPreparation.LoadLedgerDirectory(
                    context.LedgerPath,
                    "existing frozen ledger").RawBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                throw new InvalidOperationException(
                    "accepted event files changed while ledger-recoordinate was validating them");
            }

            DagLedgerAppendWriter.WriteNewEvents(
                context.LedgerPath,
                candidateSyntax.Lines,
                context.Baseline.Events.Length,
                context.BaselineBytes);
            var appended = candidate.Events
                .Skip(context.Baseline.Events.Length)
                .OfType<FrozenLedgerEvent.EnvironmentRecoordinate>()
                .ToImmutableArray();

            var output = $"LEDGER_RECOORDINATE appended_recoordinates={appended.Length} "
                + $"requires_reattest={generation.ReattestPaths.Length} "
                + $"events={candidate.Events.Length} head={candidate.HeadHash}\n"
                + string.Concat(generation.RecoordinatedPaths.Select(static path =>
                    $"RECOORDINATED {path.Value}\n"));
            return new CommandResult(true, output, string.Empty);
        }
        catch (Exception exception) when (
            exception is ArgumentException
                or FormatException
                or IOException
                or InvalidOperationException
                or JsonException
                or KeyNotFoundException
                or UnauthorizedAccessException
                or DagLedgerCommandPreparation.LeanReportUnusableException
                or DagLedgerCommandPreparation.RepositoryUnavailableException)
        {
            return new CommandResult(
                false,
                string.Empty,
                DagLedgerAppendWriter.RenderFailure("LEDGER_RECOORDINATE_FAILED", exception));
        }
    }

    private static string RenderReattestPaths(IEnumerable<RepoPath> paths) =>
        string.Concat(paths.Select(static path => $"REQUIRES_REATTEST {path.Value}\n"));
}
