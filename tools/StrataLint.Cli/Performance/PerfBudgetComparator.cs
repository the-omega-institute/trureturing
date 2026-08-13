using System.Globalization;
using System.Text.Json;

namespace StrataLint.Cli;

internal sealed record PerfBudgetResult(
    PerfBudget Budget,
    string Level,
    string Status,
    double? ActualSeconds,
    double? OverBySeconds,
    int SampleCount);

internal static class PerfBudgetComparator
{
    internal static IReadOnlyList<PerfBudgetResult> Compare(
        IEnumerable<PerfBudget> budgets,
        IEnumerable<PerfSeriesSummary> summaries)
    {
        ArgumentNullException.ThrowIfNull(budgets);
        ArgumentNullException.ThrowIfNull(summaries);
        var summaryByKey = summaries.ToDictionary(
            static item => new SeriesKey(item.Cohort, item.WorkloadId, item.Kind, item.Stage));

        return budgets
            .OrderBy(static item => item.Id, StringComparer.Ordinal)
            .Select(budget => CompareOne(budget, summaryByKey))
            .ToArray();
    }

    private static PerfBudgetResult CompareOne(
        PerfBudget budget,
        IReadOnlyDictionary<SeriesKey, PerfSeriesSummary> summaries)
    {
        var key = new SeriesKey(budget.Cohort, budget.WorkloadId, budget.Kind, budget.Stage);
        if (!summaries.TryGetValue(key, out var summary) || summary.P95Seconds is null)
        {
            return new PerfBudgetResult(budget, "INFO", "no-data", null, null, 0);
        }

        var actual = summary.P95Seconds.Value;
        var overBy = Math.Max(0, actual - budget.LimitSeconds);
        return overBy > 0
            ? new PerfBudgetResult(
                budget,
                "WARN",
                "over-budget",
                actual,
                overBy,
                summary.ComparableSampleCount)
            : new PerfBudgetResult(
                budget,
                "INFO",
                "within-budget",
                actual,
                0,
                summary.ComparableSampleCount);
    }

    private sealed record SeriesKey(
        PerfCohort Cohort,
        string WorkloadId,
        string Kind,
        string Stage);
}

internal static class PerfBudgetRenderer
{
    private const string ResultSchema = "stratalint-perf-budget-result-v1";

    internal static string Render(IReadOnlyList<PerfBudgetResult> results)
    {
        if (results.Count == 0) return string.Empty;
        return string.Join('\n', results.Select(static item => JsonSerializer.Serialize(new
        {
            schema = ResultSchema,
            level = item.Level,
            status = item.Status,
            budget_id = item.Budget.Id,
            mode = item.Budget.Mode,
            cohort = new
            {
                venue = item.Budget.Cohort.Venue,
                os = item.Budget.Cohort.Os,
                arch = item.Budget.Cohort.Arch,
                cpu_class = item.Budget.Cohort.CpuClass,
                runner_class = item.Budget.Cohort.RunnerClass,
            },
            workload_id = item.Budget.WorkloadId,
            kind = item.Budget.Kind,
            stage = item.Budget.Stage,
            metric = item.Budget.Metric,
            sample_count = item.SampleCount,
            actual_seconds = item.ActualSeconds,
            limit_seconds = item.Budget.LimitSeconds,
            over_by_seconds = item.OverBySeconds,
            owner = item.Budget.Owner,
            review_due = item.Budget.ReviewDue.ToString("yyyy-MM-dd", CultureInfo.InvariantCulture),
            false_positive_window_days = item.Budget.FalsePositiveWindowDays,
            false_positive_rate_percent = item.Budget.FalsePositiveRatePercent,
        }))) + "\n";
    }
}
