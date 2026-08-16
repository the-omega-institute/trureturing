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
            if (candidateBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                return new CommandResult(
                    true,
                    $"LEDGER_REATTEST no changed frozen modules events={context.Baseline.Events.Length} head={context.Baseline.HeadHash}\n",
                    string.Empty);
            }

            var intermediateSyntax = DagLedgerCommandPreparation.LoadLedger(
                candidateBytes.AsSpan(),
                "generated frozen ledger");
            var intermediateReferences = DagLedgerCommandPreparation.ScanReferences(
                intermediateSyntax,
                "generated frozen ledger");
            var trustedIntermediateReferences = repository.ValidateFrozenReferences(
                intermediateReferences);
            var intermediate = FrozenLedger.ValidateHistoryPrefix(
                intermediateSyntax,
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
            var generatedReferences = DagLedgerCommandPreparation.ScanReferences(
                generatedSyntax,
                "generated frozen ledger");
            var trustedGeneratedReferences = repository.ValidateFrozenReferences(generatedReferences);
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
            var baselineFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(
                context.LedgerPath);
            var currentBaselineSyntax = DagLedgerCommandPreparation.LoadLedgerFiles(
                baselineFiles,
                "existing frozen ledger");
            if (!currentBaselineSyntax.RawBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                throw new InvalidOperationException(
                    "accepted event files changed while ledger-reattest was validating them");
            }

            var newFiles = DagLedgerAppendWriter.BuildNewEventFiles(
                generatedSyntax.Lines,
                context.Baseline.Events.Length,
                currentBaselineSyntax);
            var simulatedFiles = baselineFiles.AddRange(newFiles);
            var simulatedEvents = LoadFileEvents(simulatedFiles, "prospective frozen ledger");
            var simulatedSyntax = DagLedgerCommandPreparation.LoadLedgerFiles(
                simulatedFiles,
                "prospective frozen ledger");
            var simulatedReferences = DagLedgerCommandPreparation.ScanReferences(
                simulatedSyntax,
                "prospective frozen ledger");
            var trustedSimulatedReferences = repository.ValidateFrozenReferences(simulatedReferences);
            var replayed = FrozenLedger.ValidateHistory(
                simulatedSyntax,
                context.Catalog,
                trustedSimulatedReferences) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "prospective frozen ledger history is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            RequireExpectedEventSet(
                LoadFileEvents(baselineFiles, "existing frozen ledger"),
                LoadFileEvents(newFiles, "generated frozen ledger suffix"),
                simulatedEvents);
            if (!SameActiveSet(candidate, replayed)
                || !candidate.RevokedFrozenNodeIds.SetEquals(replayed.RevokedFrozenNodeIds))
            {
                throw new InvalidOperationException(
                    "prospective content-addressed ledger replay does not retain the validated candidate state");
            }
            if (!DagLedgerCommandPreparation.LoadLedgerDirectory(
                    context.LedgerPath,
                    "existing frozen ledger").RawBytes.AsSpan().SequenceEqual(context.BaselineBytes))
            {
                throw new InvalidOperationException(
                    "accepted event files changed while ledger-reattest was validating them");
            }

            DagLedgerAppendWriter.WriteEventFiles(
                context.LedgerPath,
                newFiles,
                context.BaselineBytes);
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
                + $"events={replayed.Events.Length} head={replayed.HeadHash}\n"
                + string.Concat(appended.Select(item =>
                    $"REATTESTED {context.Baseline.ActiveEntries[item.Payload.CaseId].Material.RepoPath.Value}\n"))
                + string.Concat(appendedFreezes.Select(static item =>
                    $"FROZEN {item.Payload.NodePath.Value}\n"));
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

    private static ImmutableArray<DagLedgerFileEvent> LoadFileEvents(
        IEnumerable<RepositoryFile> files,
        string label) =>
        DagLedgerLoader.LoadFiles(files) switch
        {
            DagLedgerFilesLoadOutcome.Loaded loaded => loaded.Events,
            DagLedgerFilesLoadOutcome.Invalid invalid => throw new InvalidOperationException(
                label + " syntax is invalid: " + invalid.Message),
            _ => throw new InvalidOperationException("unknown ledger files load outcome"),
        };

    private static bool SameActiveSet(
        FrozenLedgerConsistent candidate,
        FrozenLedgerConsistent replayed)
    {
        var expected = candidate.ActiveEntries.Values.ToDictionary(
            static entry => entry.Material.RepoPath.Value,
            static entry => entry.Material.FrozenNodeId.Value,
            StringComparer.Ordinal);
        var actual = replayed.ActiveEntries.Values.ToDictionary(
            static entry => entry.Material.RepoPath.Value,
            static entry => entry.Material.FrozenNodeId.Value,
            StringComparer.Ordinal);
        return expected.Count == actual.Count
            && expected.All(item =>
                actual.TryGetValue(item.Key, out var frozenNodeId)
                && string.Equals(item.Value, frozenNodeId, StringComparison.Ordinal));
    }
}
