using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerReattestWriter
{
    internal static CommandResult Reattest(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--candidate-lean-report")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-reattest --candidate-lean-report FILE");
            }

            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                arguments[1]);
            var candidateBytes = FrozenLedgerGenerator.AppendReattestation(
                context.Baseline,
                context.Catalog);
            if (candidateBytes.IsEmpty)
            {
                return new CommandResult(
                    true,
                    $"LEDGER_REATTEST no changed frozen modules events={context.Baseline.Events.Length} head={context.Baseline.HeadHash}\n",
                    string.Empty);
            }

            var intermediateSyntax = DagLedgerCommandPreparation.LoadLedger(
                candidateBytes.AsSpan(),
                "generated frozen ledger");
            var intermediateReferences = DagLedgerCommandPreparation.ScanSuffixReferences(
                intermediateSyntax,
                context.Baseline,
                "generated frozen ledger");
            var trustedIntermediateReferences = TrustedFrozenGitReferences.CreateForTrustedAdapter(
                intermediateReferences.Inputs,
                intermediateReferences.EnvironmentReferences);
            var intermediate = FrozenLedger.ValidateCandidatePrefix(
                intermediateSyntax,
                context.Baseline,
                context.Catalog,
                trustedIntermediateReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            candidateBytes = FrozenLedgerGenerator.AppendMissingFreezes(
                intermediate,
                context.Catalog);
            var generatedSyntax = DagLedgerCommandPreparation.LoadLedger(
                candidateBytes.AsSpan(),
                "generated frozen ledger");
            var trustedGeneratedReferences = DagLedgerCommandPreparation.ValidateSuffixReferences(
                repository,
                generatedSyntax,
                context.Baseline,
                "generated frozen ledger");
            var candidate = FrozenLedger.ValidateCandidate(
                generatedSyntax,
                context.Baseline,
                context.Catalog,
                trustedGeneratedReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            var baselineFiles = context.BaselineFiles;
            DagLedgerAppendWriter.RequireUnchangedBaseline(
                context.LedgerPath,
                baselineFiles,
                "ledger-reattest");

            var newFiles = DagLedgerAppendWriter.BuildNewEventFiles(
                generatedSyntax.Lines,
                knownDagHashes: context.BaseView.EventHashes);
            var prospective = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
                context.BaseView,
                newFiles,
                "generated frozen ledger suffix");
            DagLedgerAppendWriter.RequireUnchangedBaseline(
                context.LedgerPath,
                baselineFiles,
                "ledger-reattest");

            DagLedgerAppendWriter.WriteEventFiles(
                context.LedgerPath,
                newFiles,
                baselineFiles);
            var appended = candidate.Events
                .Skip(context.Baseline.Events.Length)
                .OfType<FrozenLedgerEvent.Reattest>()
                .ToImmutableArray();
            var appendedFreezes = candidate.Events
                .Skip(context.Baseline.Events.Length)
                .OfType<FrozenLedgerEvent.Freeze>()
                .ToImmutableArray();
            var output = $"LEDGER_REATTEST appended_reattests={appended.Length} "
                + $"appended_freezes={appendedFreezes.Length} "
                + $"events={context.BaseView.EventCount + newFiles.Length} "
                + $"head={context.BaseView.EventSetRoot(prospective.Select(static item => item.EventHash))}\n"
                + string.Concat(appended.Select(item =>
                    $"REATTESTED {context.Baseline.ActiveEntries[item.Payload.CaseId].Material.RepoPath.Value}\n"))
                + string.Concat(appendedFreezes.Select(static item =>
                    $"FROZEN {item.Payload.Input.DescriptorSelector}\n"));
            return new CommandResult(true, output, string.Empty);
        }
        // Preparation marks report and repository faults now. Without these two the wrapped
        // forms escape this catch and the command loses its own diagnostic.
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
                DagLedgerAppendWriter.RenderFailure("LEDGER_REATTEST_FAILED", exception));
        }
    }

    internal static void RequireExpectedEventSet(
        ImmutableArray<DagLedgerFileEvent> baselineEvents,
        ImmutableArray<DagLedgerFileEvent> newEvents,
        ImmutableArray<DagLedgerFileEvent> simulatedEvents)
    {
        var expected = baselineEvents
            .Concat(newEvents)
            .Select(static item => item.EventHash)
            .ToHashSet(StringComparer.Ordinal);
        var actual = simulatedEvents
            .Select(static item => item.EventHash)
            .ToHashSet(StringComparer.Ordinal);
        if (expected.Count != baselineEvents.Length + newEvents.Length
            || actual.Count != simulatedEvents.Length
            || !expected.SetEquals(actual))
        {
            throw new InvalidOperationException(
                "prospective content-addressed ledger event set is not exactly the baseline plus generated events");
        }
    }

}
