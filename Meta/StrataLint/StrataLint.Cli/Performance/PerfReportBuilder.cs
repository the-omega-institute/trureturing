namespace StrataLint.Cli;

internal sealed record PerfSeriesSummary(
    PerfCohort Cohort,
    string WorkloadId,
    string Kind,
    string Stage,
    int ComparableSampleCount,
    int ObservationCount,
    int FailedCount,
    int SkippedCount,
    double? P50Seconds,
    double? P95Seconds,
    IReadOnlyList<double> RecentSeconds);

internal static class PerfReportBuilder
{
    internal static IReadOnlyList<PerfSeriesSummary> Build(
        IEnumerable<PerfEvent> events,
        int recentCount)
    {
        ArgumentNullException.ThrowIfNull(events);
        if (recentCount <= 0)
        {
            throw new ArgumentOutOfRangeException(nameof(recentCount), "recent count must be positive");
        }

        return events
            .GroupBy(static item => new SeriesKey(
                item.Cohort,
                item.Context.WorkloadId,
                item.Kind,
                item.Stage))
            .Select(group => Summarize(group.Key, group, recentCount))
            .OrderBy(static item => item.Cohort.Venue, StringComparer.Ordinal)
            .ThenBy(static item => item.Cohort.Os, StringComparer.Ordinal)
            .ThenBy(static item => item.Cohort.Arch, StringComparer.Ordinal)
            .ThenBy(static item => item.Cohort.CpuClass, StringComparer.Ordinal)
            .ThenBy(static item => item.Cohort.RunnerClass, StringComparer.Ordinal)
            .ThenBy(static item => item.WorkloadId, StringComparer.Ordinal)
            .ThenBy(static item => item.Kind, StringComparer.Ordinal)
            .ThenBy(static item => item.Stage, StringComparer.Ordinal)
            .ToArray();
    }

    private static PerfSeriesSummary Summarize(
        SeriesKey key,
        IEnumerable<PerfEvent> source,
        int recentCount)
    {
        var items = source.OrderBy(static item => item.Timestamp).ToArray();
        var comparable = items
            .Where(static item => item.Status == "passed" && item.ElapsedSeconds is not null)
            .ToArray();
        var timings = comparable
            .Select(static item => item.ElapsedSeconds!.Value)
            .Order()
            .ToArray();
        var recent = comparable
            .TakeLast(recentCount)
            .Select(static item => item.ElapsedSeconds!.Value)
            .ToArray();
        return new PerfSeriesSummary(
            key.Cohort,
            key.WorkloadId,
            key.Kind,
            key.Stage,
            comparable.Length,
            items.Count(static item => item.Status == "observation"),
            items.Count(static item => item.Status == "failed"),
            items.Count(static item => item.Status == "skipped"),
            Percentile(timings, 0.50),
            Percentile(timings, 0.95),
            recent);
    }

    private static double? Percentile(IReadOnlyList<double> values, double percentile)
    {
        if (values.Count == 0) return null;
        var rank = Math.Max(1, (int)Math.Ceiling(percentile * values.Count));
        return values[rank - 1];
    }

    private sealed record SeriesKey(
        PerfCohort Cohort,
        string WorkloadId,
        string Kind,
        string Stage);
}
