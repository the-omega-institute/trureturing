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
            var generatedBytes = FrozenLedgerGenerator.AppendSynchronization(
                context.Baseline,
                context.Catalog);
            var generatedSyntax = DagLedgerCommandPreparation.LoadLedger(
                generatedBytes.AsSpan(),
                "generated frozen ledger");
            var trustedCandidateReferences = DagLedgerCommandPreparation.ValidateSuffixReferences(
                repository,
                generatedSyntax,
                context.Baseline,
                "generated frozen ledger");
            var generated = FrozenLedger.ValidateCandidate(
                generatedSyntax,
                context.Baseline,
                context.Catalog,
                trustedCandidateReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };

            if (generatedBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                return new CommandResult(
                    true,
                    $"LEDGER_SYNC no ledger changes events={generated.Events.Length} head={generated.HeadHash}\n",
                    string.Empty);
            }

            DagLedgerAppendWriter.RequireUnchangedBaseline(
                context.LedgerPath,
                context.BaselineFiles,
                "ledger-sync");

            var pending = DagLedgerAppendWriter.BuildNewEventFiles(
                generatedSyntax.Lines,
                context.Baseline.Events.Length,
                context.BaselineSyntax);
            _ = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
                context.BaseView,
                pending,
                "generated frozen ledger suffix");
            // Publication goes through the one shared publisher so ledger-sync inherits the
            // exclusive writer lock, the in-lock baseline compare-and-swap and stale-stage
            // reaping instead of carrying a second write path.
            DagLedgerAppendWriter.WriteEventFiles(
                context.LedgerPath,
                pending,
                context.BaselineFiles);

            var suffix = generated.Events.Skip(context.Baseline.Events.Length).ToImmutableArray();
            var reattests = suffix.OfType<FrozenLedgerEvent.Reattest>().ToImmutableArray();
            var freezes = suffix.OfType<FrozenLedgerEvent.Freeze>().ToImmutableArray();
            var output = $"LEDGER_SYNC appended_reattests={reattests.Length} "
                + $"appended_freezes={freezes.Length} events={generated.Events.Length} "
                + $"head={generated.HeadHash}\n"
                + string.Concat(reattests.Select(item =>
                    $"REATTESTED {context.Baseline.ActiveEntries[item.Payload.CaseId].Material.RepoPath.Value}\n"))
                + string.Concat(freezes.Select(static item => $"FROZEN {item.Payload.NodePath.Value}\n"));
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
                "LEDGER_SYNC_FAILED " + (exception.InnerException ?? exception).Message + "\n");
        }
    }

}
