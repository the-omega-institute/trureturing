using System.Text;
using System.Text.Json;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class PerfCommandTests
{
    [Fact]
    public void AppendRejectsIncompleteArguments()
    {
        using var repository = new TemporaryDirectory();

        var result = PerfAppendCommand.Run(repository.Path, ["--input", "spool.jsonl"]);

        Assert.False(result.Success);
        Assert.Contains("USAGE: StrataLint perf-append", result.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ReportRendersComparableAndObservationColumnsSeparately()
    {
        using var ledgerHome = new TemporaryDirectory();
        var ledger = Path.Combine(ledgerHome.Path, "events.jsonl");
        File.WriteAllText(
            ledger,
            EventJson("run-1", "passed", 10)
                + "\n"
                + EventJson("run-2", "observation", 200)
                + "\n",
            new UTF8Encoding(false));

        var result = PerfReportCommand.Run(["--ledger", ledger, "--recent", "5"]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"schema\":\"stratalint-perf-report-v1\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"sample_count\":1", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"p50_seconds\":10", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"p95_seconds\":10", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"observation_count\":1", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"failed_count\":0", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"skipped_count\":0", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain("200", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void ReportEmitsWarnOnlyBudgetRowsWithoutFailing()
    {
        using var ledgerHome = new TemporaryDirectory();
        var ledger = Path.Combine(ledgerHome.Path, "events.jsonl");
        var budgets = Path.Combine(ledgerHome.Path, "perf-budgets.toml");
        File.WriteAllText(ledger, EventJson("run-1", "passed", 120) + "\n", new UTF8Encoding(false));
        File.WriteAllText(
            budgets,
            """
            schema = "stratalint-perf-budget-v1"

            [[budgets]]
            id = "test-budget"
            mode = "warn-only"
            venue = "local"
            os = "Darwin"
            arch = "arm64"
            cpu_class = "Apple-M4"
            workload_id = "gate"
            kind = "timing"
            stage = "test"
            metric = "p95_seconds"
            limit_seconds = 100
            owner = "harness/performance"
            review_due = "2026-08-20"
            remediation = "Profile the test stage."
            false_positive_window_days = 14
            false_positive_rate_percent = "unmeasured"
            rollback_criteria = "Revert to warn-only if false positives reach 5 percent."
            source = "synthetic deterministic test"
            """ + "\n",
            new UTF8Encoding(false));

        var result = PerfReportCommand.Run(
            ["--ledger", ledger, "--recent", "5", "--budgets", budgets]);

        Assert.True(result.Success, result.Error);
        Assert.Contains("\"schema\":\"stratalint-perf-budget-result-v1\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"level\":\"WARN\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"status\":\"over-budget\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"actual_seconds\":120", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"limit_seconds\":100", result.Output, StringComparison.Ordinal);
    }

    private static string EventJson(string runId, string status, double elapsed) =>
        JsonSerializer.Serialize(new
        {
            schema = "stratalint-perf-event-v1",
            run_id = runId,
            ts = "2026-07-19T12:00:00Z",
            cohort = new
            {
                venue = "local",
                os = "Darwin",
                arch = "arm64",
                cpu_class = "Apple-M4",
                runner_class = (string?)null,
            },
            context = new
            {
                commit = "0123456789abcdef0123456789abcdef01234567",
                @base = "fedcba9876543210fedcba9876543210fedcba98",
                workload_id = "gate",
                cache_state = "warm",
                loadavg_per_cpu = 0.25,
                host_concurrency = 1,
            },
            kind = "timing",
            stage = "test",
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
