using System.Text;
using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class PerfLedgerTests
{
    [Fact]
    public void MissingCriticalContextForcesObservation()
    {
        var parsed = PerfEventCodec.ParseLine(EventJson(
            status: "passed",
            loadavgPerCpu: 0.25,
            hostConcurrency: null));

        Assert.Equal("observation", parsed.Status);
    }

    [Fact]
    public void RequiredEnvelopeFieldCannotBeOmitted()
    {
        var json = EventJson().Replace(
            "\"workload_id\":\"gate\",",
            string.Empty,
            StringComparison.Ordinal);

        var exception = Assert.Throws<InvalidOperationException>(() =>
            PerfEventCodec.ParseLine(json));

        Assert.Contains("context.workload_id", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void WriterCanonicalizesAndAppendsOnlyOutsideRepository()
    {
        using var repository = new TemporaryDirectory();
        using var external = new TemporaryDirectory();
        var input = Path.Combine(repository.Path, "events-spool.jsonl");
        var ledger = Path.Combine(external.Path, "events.jsonl");
        File.WriteAllText(
            input,
            EventJson(status: "passed", hostConcurrency: null) + "\n",
            new UTF8Encoding(false));

        var count = PerfLedgerWriter.Append(repository.Path, input, ledger);

        Assert.Equal(1, count);
        var line = Assert.Single(File.ReadAllLines(ledger));
        using var document = JsonDocument.Parse(line);
        Assert.Equal("stratalint-perf-event-v1", document.RootElement.GetProperty("schema").GetString());
        Assert.Equal("observation", document.RootElement.GetProperty("status").GetString());

        var inside = Path.Combine(repository.Path, "events.jsonl");
        Assert.Throws<InvalidOperationException>(() =>
            PerfLedgerWriter.Append(repository.Path, input, inside));
    }

    [Fact]
    public void ReportKeepsCohortsSeparateAndExcludesObservationsFromPercentiles()
    {
        var events = new[]
        {
            PerfEventCodec.ParseLine(EventJson(runId: "run-1", elapsed: 1)),
            PerfEventCodec.ParseLine(EventJson(runId: "run-2", elapsed: 2)),
            PerfEventCodec.ParseLine(EventJson(runId: "run-3", elapsed: 3)),
            PerfEventCodec.ParseLine(EventJson(runId: "run-4", elapsed: 4)),
            PerfEventCodec.ParseLine(EventJson(runId: "run-5", elapsed: 100)),
            PerfEventCodec.ParseLine(EventJson(
                runId: "run-observation",
                status: "observation",
                elapsed: 999)),
            PerfEventCodec.ParseLine(EventJson(
                runId: "run-skipped",
                status: "skipped",
                elapsed: 0)),
            PerfEventCodec.ParseLine(EventJson(
                runId: "run-failed",
                status: "failed",
                elapsed: 500)),
            PerfEventCodec.ParseLine(EventJson(
                runId: "run-ci",
                venue: "ci",
                runnerClass: "hosted-arm64",
                elapsed: 50)),
        };

        var report = PerfReportBuilder.Build(events, recentCount: 3);

        Assert.Equal(2, report.Count);
        var local = Assert.Single(report, static item => item.Cohort.Venue == "local");
        Assert.Equal("gate", local.WorkloadId);
        Assert.Equal("engineering-test", local.Stage);
        Assert.Equal(5, local.ComparableSampleCount);
        Assert.Equal(1, local.ObservationCount);
        Assert.Equal(1, local.SkippedCount);
        Assert.Equal(1, local.FailedCount);
        Assert.Equal(3, local.P50Seconds);
        Assert.Equal(100, local.P95Seconds);
        Assert.Equal(new double[] { 3, 4, 100 }, local.RecentSeconds);

        var ci = Assert.Single(report, static item => item.Cohort.Venue == "ci");
        Assert.Equal(1, ci.ComparableSampleCount);
        Assert.Equal(50, ci.P50Seconds);
        Assert.Equal(50, ci.P95Seconds);
    }

    private static string EventJson(
        string runId = "run-local",
        string status = "passed",
        string venue = "local",
        string? runnerClass = null,
        double? loadavgPerCpu = 0.25,
        int? hostConcurrency = 1,
        double elapsed = 12) => JsonSerializer.Serialize(new
        {
            schema = "stratalint-perf-event-v1",
            run_id = runId,
            ts = "2026-07-19T12:00:00Z",
            cohort = new
            {
                venue,
                os = "Darwin",
                arch = "arm64",
                cpu_class = "Apple-M4",
                runner_class = runnerClass,
            },
            context = new
            {
                commit = "0123456789abcdef0123456789abcdef01234567",
                @base = "fedcba9876543210fedcba9876543210fedcba98",
                workload_id = "gate",
                cache_state = "warm",
                loadavg_per_cpu = loadavgPerCpu,
                host_concurrency = hostConcurrency,
            },
            kind = "timing",
            stage = "engineering-test",
            status,
            elapsed_seconds = elapsed,
            resources = new
            {
                disk_free_gb = 80.5,
                fd_peak = (int?)null,
                rss_peak_mb = (double?)null,
            },
        });
}
