using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DagLedgerRevokeWriter
{
    internal static CommandResult Revoke(
        string repositoryRoot,
        IRepositoryGateway repository,
        IReadOnlyList<string> arguments)
    {
        try
        {
            var (reportPath, receiptOids) = ParseArguments(arguments);
            var context = DagLedgerCommandPreparation.Prepare(
                repositoryRoot,
                repository,
                reportPath);
            var receipts = TrustedRevocationReceiptStore.Materialize(
                context.Baseline,
                context.Snapshot,
                receiptOids) switch
            {
                RevocationReceiptStoreOutcome.Accepted accepted => accepted.Capability,
                RevocationReceiptStoreOutcome.Rejected rejected =>
                    throw new FormatException(rejected.Message),
            };
            var validated = receipts.Evidence.Select(evidence =>
                RevocationEvidenceValidator.Validate(evidence, context.Baseline, receipts) switch
                {
                    RevocationEvidenceValidationOutcome.Accepted accepted => accepted.Capability,
                    RevocationEvidenceValidationOutcome.Rejected rejected =>
                        throw new FormatException(rejected.Message),
                }).ToImmutableArray();
            var plan = RevocationPlanner.Plan(context.Baseline, validated) switch
            {
                RevocationPlanOutcome.Accepted accepted => accepted.Capability,
                RevocationPlanOutcome.Rejected rejected => throw new FormatException(rejected.Message),
            };
            var affected = plan.AffectedFrozenNodeIds.ToHashSet();
            var eventFiles = context.BaseView.ActiveByPath.Values
                .Where(entry => affected.Contains(entry.Material.FrozenNodeId))
                .Select(entry => context.BaselineFiles.Single(file =>
                    file.Path.Value.EndsWith(
                        entry.EventHash[7..] + ".json",
                        StringComparison.Ordinal)))
                .ToImmutableArray();
            DagLedgerAppendWriter.DeleteEventFiles(
                context.LedgerPath,
                eventFiles,
                context.BaselineFiles);
            return new CommandResult(
                true,
                $"LEDGER_REVOKE removed_freezes={eventFiles.Length} "
                    + $"events={context.BaseView.EventCount - eventFiles.Length}\n",
                string.Empty);
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
                DagLedgerAppendWriter.RenderFailure("LEDGER_REVOKE_FAILED", exception));
        }
    }

    private static (string ReportPath, ImmutableArray<string> ReceiptOids) ParseArguments(
        IReadOnlyList<string> arguments)
    {
        if (arguments.Count < 4
            || arguments[0] != "--candidate-lean-report"
            || arguments.Count % 2 != 0)
        {
            throw new InvalidOperationException(
                "USAGE: StrataLint ledger-revoke --candidate-lean-report FILE --receipt-blob-oid OID [...]");
        }

        var receipts = ImmutableArray.CreateBuilder<string>();
        for (var index = 2; index < arguments.Count; index += 2)
        {
            if (arguments[index] != "--receipt-blob-oid")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint ledger-revoke --candidate-lean-report FILE --receipt-blob-oid OID [...]");
            }

            receipts.Add(arguments[index + 1]);
        }

        return (arguments[1], receipts.ToImmutable());
    }
}
