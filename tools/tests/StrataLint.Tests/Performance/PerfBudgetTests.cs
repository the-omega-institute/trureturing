using System.Text;
using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed class PerfBudgetTests
{
    [Fact]
    public void CanonicalCatalogRegistersThreeObservableWarnOnlySessionBudgets()
    {
        var root = TestRepositoryLayout.FindRoot();

        var catalog = PerfBudgetLoader.LoadFile(Path.Combine(root, "Golden", "perf-budgets.toml"));

        Assert.Equal(3, catalog.Budgets.Count);
        Assert.All(catalog.Budgets, static budget =>
        {
            Assert.Equal("warn-only", budget.Mode);
            Assert.Null(budget.FalsePositiveRatePercent);
            Assert.Equal(new DateOnly(2026, 8, 20), budget.ReviewDue);
        });
        Assert.Equal(
            new[] { 120d, 1_380d, 1_560d },
            catalog.Budgets.Select(static budget => budget.LimitSeconds).Order().ToArray());
    }

    [Fact]
    public void LoaderRequiresCompleteWarnOnlyObligations()
    {
        using var directory = new TemporaryDirectory();
        var path = Path.Combine(directory.Path, "perf-budgets.toml");
        File.WriteAllText(path, BudgetToml(), new UTF8Encoding(false));

        var catalog = PerfBudgetLoader.LoadFile(path);

        var budget = Assert.Single(catalog.Budgets);
        Assert.Equal("local-gate-total", budget.Id);
        Assert.Equal("warn-only", budget.Mode);
        Assert.Equal("local", budget.Cohort.Venue);
        Assert.Null(budget.Cohort.RunnerClass);
        Assert.Equal("local-harness-gate", budget.WorkloadId);
        Assert.Equal("timing", budget.Kind);
        Assert.Equal("total", budget.Stage);
        Assert.Equal("p95_seconds", budget.Metric);
        Assert.Equal(1_380, budget.LimitSeconds);
        Assert.Equal("harness/performance", budget.Owner);
        Assert.Equal(new DateOnly(2026, 8, 20), budget.ReviewDue);
        Assert.Equal(14, budget.FalsePositiveWindowDays);
        Assert.Null(budget.FalsePositiveRatePercent);
        Assert.Contains("1138s", budget.Source, StringComparison.Ordinal);
        Assert.NotEmpty(budget.Remediation);
        Assert.NotEmpty(budget.RollbackCriteria);
    }

    [Fact]
    public void LoaderRejectsDuplicateSeriesKeys()
    {
        using var directory = new TemporaryDirectory();
        var path = Path.Combine(directory.Path, "perf-budgets.toml");
        var duplicate = BudgetToml() + BudgetTable("duplicate", 1_500);
        File.WriteAllText(path, duplicate, new UTF8Encoding(false));

        var exception = Assert.Throws<InvalidOperationException>(() =>
            PerfBudgetLoader.LoadFile(path));

        Assert.Contains("duplicate budget series", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void ComparatorMatchesTheCompleteSeriesKeyAndOrdersResultsByBudgetId()
    {
        using var directory = new TemporaryDirectory();
        var path = Path.Combine(directory.Path, "perf-budgets.toml");
        File.WriteAllText(
            path,
            "schema = \"stratalint-perf-budget-v1\"\n\n"
                + BudgetTable("z-over", 100)
                + BudgetTable("a-no-data", 200, cpuClass: "other-cpu"),
            new UTF8Encoding(false));
        var budgets = PerfBudgetLoader.LoadFile(path).Budgets;
        var summary = new PerfSeriesSummary(
            new PerfCohort("local", "Darwin", "arm64", "Apple M4 Pro", null),
            "local-harness-gate",
            "timing",
            "total",
            5,
            0,
            0,
            0,
            80,
            120,
            [80, 90, 100, 110, 120]);

        var results = PerfBudgetComparator.Compare(budgets, [summary]);

        Assert.Equal(new[] { "a-no-data", "z-over" }, results.Select(static item => item.Budget.Id));
        Assert.Equal("no-data", results[0].Status);
        Assert.Equal("INFO", results[0].Level);
        Assert.Null(results[0].ActualSeconds);
        Assert.Equal("over-budget", results[1].Status);
        Assert.Equal("WARN", results[1].Level);
        Assert.Equal(120, results[1].ActualSeconds);
        Assert.Equal(20, results[1].OverBySeconds);
    }

    [Fact]
    public void ComparatorDoesNotWarnAtTheBudgetBoundary()
    {
        using var directory = new TemporaryDirectory();
        var path = Path.Combine(directory.Path, "perf-budgets.toml");
        File.WriteAllText(path, BudgetToml(limitSeconds: 120), new UTF8Encoding(false));
        var budget = Assert.Single(PerfBudgetLoader.LoadFile(path).Budgets);
        var summary = new PerfSeriesSummary(
            budget.Cohort,
            budget.WorkloadId,
            budget.Kind,
            budget.Stage,
            1,
            0,
            0,
            0,
            120,
            120,
            [120]);

        var result = Assert.Single(PerfBudgetComparator.Compare([budget], [summary]));

        Assert.Equal("within-budget", result.Status);
        Assert.Equal("INFO", result.Level);
        Assert.Equal(0, result.OverBySeconds);
    }

    [Theory]
    [InlineData("venue")]
    [InlineData("os")]
    [InlineData("arch")]
    [InlineData("cpu_class")]
    [InlineData("runner_class")]
    [InlineData("workload_id")]
    [InlineData("kind")]
    [InlineData("stage")]
    public void ComparatorRejectsDriftInEverySeriesKeyDimension(string dimension)
    {
        using var directory = new TemporaryDirectory();
        var path = Path.Combine(directory.Path, "perf-budgets.toml");
        File.WriteAllText(path, BudgetToml(limitSeconds: 100), new UTF8Encoding(false));
        var budget = Assert.Single(PerfBudgetLoader.LoadFile(path).Budgets);
        var cohort = budget.Cohort;
        var workloadId = budget.WorkloadId;
        var kind = budget.Kind;
        var stage = budget.Stage;
        switch (dimension)
        {
            case "venue": cohort = cohort with { Venue = "ci" }; break;
            case "os": cohort = cohort with { Os = "Linux" }; break;
            case "arch": cohort = cohort with { Arch = "x86_64" }; break;
            case "cpu_class": cohort = cohort with { CpuClass = "other-cpu" }; break;
            case "runner_class": cohort = cohort with { RunnerClass = "runner-1" }; break;
            case "workload_id": workloadId = "preflight"; break;
            case "kind": kind = "resource"; break;
            case "stage": stage = "admission"; break;
            default: throw new InvalidOperationException("unknown test dimension");
        }
        var summary = new PerfSeriesSummary(
            cohort,
            workloadId,
            kind,
            stage,
            1,
            0,
            0,
            0,
            120,
            120,
            [120]);

        var result = Assert.Single(PerfBudgetComparator.Compare([budget], [summary]));

        Assert.Equal("no-data", result.Status);
        Assert.Equal("INFO", result.Level);
    }

    private static string BudgetToml(double limitSeconds = 1_380) =>
        "schema = \"stratalint-perf-budget-v1\"\n\n"
        + BudgetTable("local-gate-total", limitSeconds);

    private static string BudgetTable(
        string id,
        double limitSeconds,
        string cpuClass = "Apple M4 Pro") => $$"""
        [[budgets]]
        id = "{{id}}"
        mode = "warn-only"
        venue = "local"
        os = "Darwin"
        arch = "arm64"
        cpu_class = "{{cpuClass}}"
        workload_id = "local-harness-gate"
        kind = "timing"
        stage = "total"
        metric = "p95_seconds"
        limit_seconds = {{limitSeconds}}
        owner = "harness/performance"
        review_due = "2026-08-20"
        remediation = "Profile the named stage and attach same-cohort evidence."
        false_positive_window_days = 14
        false_positive_rate_percent = "unmeasured"
        rollback_criteria = "Revert to warn-only if false positives reach 5 percent."
        source = "2026-07-20 session: gate 1138s; rounded with headroom."

        """;

}
