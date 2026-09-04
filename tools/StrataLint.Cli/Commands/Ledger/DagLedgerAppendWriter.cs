using System.Collections.Immutable;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerAppendWriter
{
    internal static CommandResult Append(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 2 || arguments[0] != "--candidate-lean-report")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-append --candidate-lean-report FILE");
            }

            var baselineFiles = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(
                Path.Combine(
                    repositoryRoot,
                    FrozenLedgerChangeClassifier.AcceptedRoot.Replace(
                        '/',
                        Path.DirectorySeparatorChar)));

            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                arguments[1],
                trustedBaselineFiles: default);

            var drafts = FrozenLedgerGenerator.MissingFreezes(
                context.Baseline,
                context.Catalog);
            if (drafts.IsEmpty)
            {
                return new CommandResult(
                    true,
                    $"LEDGER_APPEND appended_freezes=0 no catalog reconciliation required "
                    + $"events={context.Baseline.EventCount} head={context.Baseline.HeadHash}\n",
                    string.Empty);
            }

            var pending = BuildNewEventFiles(drafts);
            var prospective = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
                context.BaseView,
                pending,
                "generated frozen ledger suffix");
            var candidate = FrozenLedger.ValidateCandidate(
                prospective,
                context.Baseline,
                context.Catalog) switch
            {
                FrozenLedgerValidationOutcome.Accepted accepted => accepted.Capability,
                FrozenLedgerValidationOutcome.Rejected rejected => throw new InvalidOperationException(
                    "generated frozen ledger is invalid: " + rejected.Message),
                _ => throw new InvalidOperationException("unknown ledger validation outcome"),
            };
            var freezes = prospective
                .Where(static item => item.EventType == "Freeze")
                .ToImmutableArray();
            FrozenLedgerPublication.PublishSnapshot(
                repositoryRoot,
                context.LedgerPath,
                context.BaselineFiles.Concat(pending),
                context.BaselineFiles,
                freezes,
                [],
                "ledger-append");

            var output = $"LEDGER_APPEND appended_freezes={freezes.Length} "
                + $"events={candidate.EventCount} "
                + $"head={context.BaseView.EventSetRoot(prospective.Select(static item => item.EventHash))}\n"
                + string.Concat(freezes.Select(static item =>
                    $"FROZEN {item.DescriptorPath.Value}\n"));
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
                RenderFailure("LEDGER_APPEND_FAILED", exception));
        }
    }







    internal static ImmutableArray<RepositoryFile> BuildNewEventFiles(
        IEnumerable<FrozenLedgerDraft> drafts)
    {
        var files = ImmutableArray.CreateBuilder<RepositoryFile>();
        foreach (var draft in drafts)
        {
            var encoded = FrozenLedgerCanonicalWriter.WriteDagEvent(
                draft.EventType,
                draft.Payload);
            var identity = FrozenLedgerCanonicalWriter.EventIdentity(encoded.Hash);
            var path = RepoPath.CreateKnown(
                $"{FrozenLedgerChangeClassifier.AcceptedRoot}/{identity[7..]}.json");
            files.Add(new RepositoryFile(
                path,
                encoded.Bytes,
                Encoding.UTF8.GetString(encoded.Bytes.AsSpan())));
        }

        return files.ToImmutable();
    }

    internal static string RenderFailure(string marker, Exception exception)
    {
        var detail = exception.InnerException is null
            ? exception.Message
            : exception.Message + " Cause: " + exception.InnerException.Message;
        return marker + " " + detail + "\n";
    }

}
