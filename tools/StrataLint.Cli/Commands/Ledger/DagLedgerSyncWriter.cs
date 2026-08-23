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
            if (!TryParseArguments(arguments, out var candidateLeanReport, out var baseRevision))
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-sync --candidate-lean-report FILE [--base REV]");
            }

            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                candidateLeanReport,
                baseRevision);
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

            if (generatedBytes.IsEmpty)
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
                knownDagHashes: context.BaseView.EventHashes);
            var prospective = DagLedgerCommandPreparation.ValidateGeneratedEventFiles(
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
                + $"head={context.BaseView.EventSetRoot(prospective.Select(static item => item.EventHash))}\n"
                + string.Concat(reattests.Select(item =>
                    $"REATTESTED {context.Baseline.ActiveEntries[item.Payload.CaseId].Material.RepoPath.Value}\n"))
                + string.Concat(freezes.Select(static item => $"FROZEN {item.Payload.Input.DescriptorSelector}\n"));
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

    /// Parses `--candidate-lean-report FILE [--base REV]` (either flag order, each at most once).
    /// `--base` is optional; omitting it leaves baseRevision null, which callers must treat as "use
    /// the default uncommitted-changes view" to keep the no-flag path byte-identical to before this
    /// flag existed (issue #2474). The value is passed through verbatim -- this parser never
    /// resolves or defaults it to a remote ref; only the caller decides what revision REV names
    /// (CLAUDE.md 第Ⅵ节 git reference discipline).
    ///
    /// A value that itself looks like a flag (starts with '-') is rejected rather than consumed:
    /// without this, `--base --cached` would feed the literal string "--cached" to
    /// GitRepositoryGateway.ReadChanges, which passes it straight through to `git diff ...
    /// <changeBase> --`. There "--cached" is not a revision but a recognized git diff flag (compare
    /// against the index), so the command would exit 0 with an empty change set -- fail-open,
    /// silently reproducing the #2474 symptom under a different cause instead of failing loudly.
    /// Rejecting any flag-shaped value here, for both flags, closes that off before it ever reaches
    /// git.
    private static bool TryParseArguments(
        IReadOnlyList<string> arguments,
        out string candidateLeanReport,
        out string? baseRevision)
    {
        candidateLeanReport = string.Empty;
        baseRevision = null;
        string? report = null;
        string? @base = null;
        var index = 0;
        while (index < arguments.Count)
        {
            if (arguments[index] == "--candidate-lean-report"
                && report is null
                && index + 1 < arguments.Count
                && !string.IsNullOrWhiteSpace(arguments[index + 1])
                && !IsFlagShaped(arguments[index + 1]))
            {
                report = arguments[index + 1];
                index += 2;
                continue;
            }

            if (arguments[index] == "--base"
                && @base is null
                && index + 1 < arguments.Count
                && !string.IsNullOrWhiteSpace(arguments[index + 1])
                && !IsFlagShaped(arguments[index + 1]))
            {
                @base = arguments[index + 1];
                index += 2;
                continue;
            }

            return false;
        }

        if (report is null)
        {
            return false;
        }

        candidateLeanReport = report;
        baseRevision = @base;
        return true;
    }

    private static bool IsFlagShaped(string value) => value.StartsWith('-');

}
