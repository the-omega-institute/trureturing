using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerSyncWriter
{
    internal static CommandResult Sync(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--candidate-lean-report")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-sync --candidate-lean-report FILE");
            }

            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                arguments[1]);
            var candidateBytes = FrozenLedgerGenerator.AppendSynchronization(
                context.Baseline,
                context.Catalog);
            var candidateSyntax = DagLedgerCommandPreparation.LoadLedger(
                candidateBytes.AsSpan(),
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

            if (candidateBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                return new CommandResult(
                    true,
                    $"LEDGER_SYNC no ledger changes events={candidate.Events.Length} head={candidate.HeadHash}\n",
                    string.Empty);
            }

            if (!DagLedgerCommandPreparation.LoadLedgerDirectory(context.LedgerPath, "existing frozen ledger")
                    .RawBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                throw new InvalidOperationException(
                    "accepted event files changed while ledger-sync was validating them");
            }

            var scratchWarning = DagLedgerAppendWriter.WriteNewEvents(
                context.LedgerPath,
                candidateSyntax.Lines,
                context.Baseline.Events.Length,
                context.BaselineBytes);
            var written = DagLedgerCommandPreparation.LoadLedgerDirectory(
                context.LedgerPath,
                "written frozen ledger");
            if (!written.RawBytes.AsSpan().SequenceEqual(candidateBytes.AsSpan()))
            {
                throw new InvalidOperationException(
                    "written ledger-sync events do not replay to the validated candidate bytes");
            }

            var suffix = candidate.Events.Skip(context.Baseline.Events.Length).ToImmutableArray();
            var reattests = suffix.OfType<FrozenLedgerEvent.Reattest>().ToImmutableArray();
            var freezes = suffix.OfType<FrozenLedgerEvent.Freeze>().ToImmutableArray();
            var output = $"LEDGER_SYNC appended_reattests={reattests.Length} "
                + $"appended_freezes={freezes.Length} events={candidate.Events.Length} "
                + $"head={candidate.HeadHash}\n"
                + string.Concat(reattests.Select(item =>
                    $"REATTESTED {context.Baseline.ActiveEntries[item.Payload.CaseId].Material.RepoPath.Value}\n"))
                + string.Concat(freezes.Select(static item => $"FROZEN {item.Payload.NodePath.Value}\n"));
            return new CommandResult(true, output, scratchWarning);
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
                DagLedgerAppendWriter.RenderFailure("LEDGER_SYNC_FAILED", exception));
        }
    }
}
