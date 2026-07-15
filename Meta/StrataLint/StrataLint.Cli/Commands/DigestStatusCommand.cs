using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestStatusCommand
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
    };

    internal static CommandResult Run(
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IScribeEmissionVerifier scribeEmissionVerifier,
        IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(scribeEmissionVerifier);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            var options = ParseArguments(arguments);
            var snapshot = Decode(repository.ReadCurrent());
            if (!snapshot.TryGetFile(BackfillInventoryLoader.RelativePath, out var ledgerFile))
            {
                throw new InvalidOperationException($"{BackfillInventoryLoader.RelativePath} is missing");
            }

            var leanReport = leanReportSource.Load(snapshot);
            var lean = ValidateLean(snapshot, leanReport);
            var verifiedScribeEmissions = scribeEmissionVerifier.Verify(leanReport);
            var document = BackfillInventoryLoader.Load(ledgerFile.Text);
            BackfillInventoryDocument? baselineDocument = null;
            if (options.BaselineRevision is not null)
            {
                var baseline = Decode(repository.ReadRevision(options.BaselineRevision));
                if (!baseline.TryGetFile(BackfillInventoryLoader.RelativePath, out var baselineLedger))
                {
                    throw new InvalidOperationException(
                        $"baseline {BackfillInventoryLoader.RelativePath} is missing");
                }

                baselineDocument = BackfillInventoryLoader.Load(baselineLedger.Text);
            }

            var evaluation = DigestionStatusEvaluator.Evaluate(
                document,
                snapshot,
                lean,
                verifiedScribeEmissions,
                baselineDocument);
            if (evaluation.Findings.Length > 0)
            {
                var error = "DIGEST_STATUS_INVALID count=" + evaluation.Findings.Length + "\n"
                    + string.Concat(evaluation.Findings.Select(static finding => $"FINDING {finding}\n"));
                return new CommandResult(false, string.Empty, error);
            }

            return new CommandResult(
                true,
                options.Json ? RenderJson(evaluation) : RenderText(evaluation),
                string.Empty);
        }
        catch (Exception exception) when (
            exception is FormatException
                or InvalidOperationException
                or IOException
                or ArgumentException)
        {
            return new CommandResult(false, string.Empty, $"DIGEST_STATUS_INVALID {exception.Message}\n");
        }
    }

    private static DigestStatusOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        var json = false;
        string? baselineRevision = null;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--json" when !json:
                    json = true;
                    break;
                case "--base" when baselineRevision is null && index + 1 < arguments.Count:
                    baselineRevision = arguments[++index];
                    if (string.IsNullOrWhiteSpace(baselineRevision)) throw Usage();
                    break;
                default:
                    throw Usage();
            }
        }

        return new DigestStatusOptions(json, baselineRevision);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint digest-status [--json] [--base REV]");

    internal static string RenderText(DigestionLedgerEvaluation evaluation)
    {
        var writer = new StringWriter(System.Globalization.CultureInfo.InvariantCulture);
        writer.WriteLine(
            $"DIGEST_STATUS entries={evaluation.Entries.Length} deletable_now={evaluation.DeletableCount}");
        foreach (var entry in evaluation.Entries
                     .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                     .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal))
        {
            writer.WriteLine("ENTRY " + entry.Render());
            foreach (var gap in entry.Gaps)
            {
                writer.WriteLine(
                    $"GAP atom={entry.Entry.AtomId} code={gap.Code} detail={JsonSerializer.Serialize(gap.Detail)}");
            }
        }

        return writer.ToString();
    }

    private static string RenderJson(DigestionLedgerEvaluation evaluation)
    {
        var material = new
        {
            schema = "stratalint-digest-status-v1",
            entries_total = evaluation.Entries.Length,
            deletable_now = evaluation.DeletableCount,
            entries = evaluation.Entries
                .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
                .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
                .Select(static item => new
                {
                    source_id = item.Entry.SourceId,
                    atom_id = item.Entry.AtomId,
                    ast_path = item.Entry.AstPath,
                    alignment = DigestionReceiptAlignmentNames.Render(item.Alignment),
                    migration = DigestionStatusNames.Migration(item.DerivedStatus.Migration),
                    truth = DigestionStatusNames.Truth(item.DerivedStatus.Truth),
                    deletable = item.Deletable,
                    gaps = item.Gaps.Select(static gap => new
                    {
                        code = gap.Code,
                        detail = gap.Detail,
                    }),
                }),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot raw) =>
        SnapshotDecoder.Decode(raw) switch
        {
            SnapshotDecodeOutcome.Decoded decoded => decoded.Snapshot,
            SnapshotDecodeOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private static AcceptedLeanClosure ValidateLean(
        RepositorySnapshot snapshot,
        LeanAxiomReport report) =>
        LeanClosureValidator.Validate(snapshot, report) switch
        {
            LeanValidationOutcome.Accepted accepted => accepted.Capability,
            LeanValidationOutcome.InfrastructureFailure failure =>
                throw new InvalidOperationException(failure.Message),
        };

    private sealed record DigestStatusOptions(bool Json, string? BaselineRevision);
}
