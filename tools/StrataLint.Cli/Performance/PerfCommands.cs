using System.Globalization;
using System.Text.Json;

namespace StrataLint.Cli;

internal static class PerfAppendCommand
{
    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        try
        {
            if (arguments.Count != 4
                || arguments[0] != "--input"
                || arguments[2] != "--ledger")
            {
                throw new InvalidOperationException(
                    "USAGE: StrataLint perf-append --input FILE --ledger FILE");
            }

            var appended = PerfLedgerWriter.Append(repositoryRoot, arguments[1], arguments[3]);
            return new CommandResult(
                true,
                $"PERF_APPEND appended={appended} schema={PerfEventCodec.Schema}\n",
                string.Empty);
        }
        catch (Exception exception) when (
            exception is ArgumentException
                or IOException
                or InvalidOperationException
                or JsonException
                or UnauthorizedAccessException)
        {
            return new CommandResult(false, string.Empty, "PERF_APPEND_FAILED " + exception.Message + "\n");
        }
    }
}

internal static class PerfReportCommand
{
    internal static CommandResult Run(IReadOnlyList<string> arguments)
    {
        try
        {
            var (ledger, recentCount, budgetPath, check) = ParseArguments(arguments);
            if (check && ledger is null)
            {
                var catalog = PerfBudgetLoader.LoadFile(budgetPath!);
                return new CommandResult(
                    true,
                    $"PERF_REPORT_CHECK schema={PerfBudgetLoader.Schema} budgets={catalog.Budgets.Count}\n",
                    string.Empty);
            }

            var events = File.Exists(ledger)
                ? File.ReadLines(ledger)
                    .Where(static line => !string.IsNullOrWhiteSpace(line))
                    .Select(PerfEventCodec.ParseLine)
                    .ToArray()
                : [];
            var summaries = PerfReportBuilder.Build(events, recentCount);
            var budgetOutput = budgetPath is null
                ? string.Empty
                : PerfBudgetRenderer.Render(PerfBudgetComparator.Compare(
                    PerfBudgetLoader.LoadFile(budgetPath).Budgets,
                    summaries));
            return new CommandResult(
                true,
                PerfReportRenderer.Render(summaries, recentCount) + budgetOutput,
                string.Empty);
        }
        catch (Exception exception) when (
            exception is ArgumentException
                or IOException
                or InvalidOperationException
                or JsonException
                or UnauthorizedAccessException)
        {
            return new CommandResult(false, string.Empty, "PERF_REPORT_FAILED " + exception.Message + "\n");
        }
    }

    private static (string? Ledger, int RecentCount, string? BudgetPath, bool Check) ParseArguments(
        IReadOnlyList<string> arguments)
    {
        string? ledger = null;
        string? budgetPath = null;
        var check = false;
        var recentCount = 10;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--check" when !check:
                    check = true;
                    break;
                case "--ledger" when ledger is null:
                    if (++index >= arguments.Count) throw Usage();
                    ledger = arguments[index];
                    break;
                case "--recent" when ++index < arguments.Count
                    && int.TryParse(
                        arguments[index],
                        NumberStyles.None,
                        CultureInfo.InvariantCulture,
                        out var parsed)
                    && parsed > 0:
                    recentCount = parsed;
                    break;
                case "--budgets" when budgetPath is null:
                    if (++index >= arguments.Count) throw Usage();
                    budgetPath = arguments[index];
                    break;
                default:
                    throw Usage();
            }
        }

        if (check && budgetPath is null) throw Usage();
        if (!check && string.IsNullOrWhiteSpace(ledger)) throw Usage();
        return (
            ledger is null ? null : Path.GetFullPath(ledger),
            recentCount,
            budgetPath is null ? null : Path.GetFullPath(budgetPath),
            check);
    }

    private static InvalidOperationException Usage() => new(
        "USAGE: StrataLint perf-report [--check] --budgets FILE | --ledger FILE [--recent N] [--budgets FILE]");
}

internal static class PerfReportRenderer
{
    private const string ReportSchema = "stratalint-perf-report-v1";

    internal static string Render(IReadOnlyList<PerfSeriesSummary> summaries, int recentCount)
    {
        var lines = new List<string>(summaries.Count + 1)
        {
            JsonSerializer.Serialize(new
            {
                schema = ReportSchema,
                recent_count = recentCount,
                series_count = summaries.Count,
            }),
        };
        lines.AddRange(summaries.Select(static item => JsonSerializer.Serialize(new
        {
            schema = ReportSchema,
            cohort = new
            {
                venue = item.Cohort.Venue,
                os = item.Cohort.Os,
                arch = item.Cohort.Arch,
                cpu_class = item.Cohort.CpuClass,
                runner_class = item.Cohort.RunnerClass,
            },
            workload_id = item.WorkloadId,
            kind = item.Kind,
            stage = item.Stage,
            sample_count = item.ComparableSampleCount,
            p50_seconds = item.P50Seconds,
            p95_seconds = item.P95Seconds,
            recent_seconds = item.RecentSeconds,
            observation_count = item.ObservationCount,
            failed_count = item.FailedCount,
            skipped_count = item.SkippedCount,
        })));
        return string.Join('\n', lines) + "\n";
    }
}
