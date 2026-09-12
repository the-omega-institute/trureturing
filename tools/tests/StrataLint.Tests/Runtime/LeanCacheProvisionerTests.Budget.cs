using StrataLint.Cli;

namespace StrataLint.Tests;


public sealed partial class LeanCacheProvisionerTests
{
    private const string BudgetVariable = "STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS";

    [Fact]
    public void ThreeNamedBudgetsExistAndCurrentlyShareTheLoadBearingValue()
    {
        var lean = LeanCacheProvisioner.LeanCommandBudget;
        var copy = LeanCacheProvisioner.DirectoryCopyBudget;
        var fetch = LeanCacheProvisioner.DependencyFetchBudget;

        Assert.Equal(
            PinnedProductionBudgets.LeanCacheProvisionBudget,
            lean);

        Assert.Equal(lean, copy);
        Assert.Equal(lean, fetch);
    }

    [Fact]
    public void AllThreeNamedBudgetsFollowTheClampedEnvironmentOverride()
    {
        var previous = Environment.GetEnvironmentVariable(BudgetVariable);
        try
        {
            Environment.SetEnvironmentVariable(BudgetVariable, "99999");
            var clamped = PinnedProductionBudgets.LeanCacheProvisionCeiling;
            Assert.Equal(clamped, LeanCacheProvisioner.LeanCommandBudget);
            Assert.Equal(clamped, LeanCacheProvisioner.DirectoryCopyBudget);
            Assert.Equal(clamped, LeanCacheProvisioner.DependencyFetchBudget);
        }
        finally
        {
            Environment.SetEnvironmentVariable(BudgetVariable, previous);
        }
    }

    [Fact]
    public void BudgetClearsTheLocalFullColdBuildWithConcurrencyHeadroom()
    {
        const int LocalFullColdBuildSeconds = 3388;

        const int ProjectedFullColdBuildSecondsAtRevision = 5763;

        Assert.True(
            LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
                > LocalFullColdBuildSeconds * 2,
            "预算未清过本地全量冷建的两倍,并发余量不足以避免重演 1800 的失败");
        Assert.True(
            LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds
                > ProjectedFullColdBuildSecondsAtRevision * 2,
            "预算未清过 #4120 修订时规模投影冷建的两倍:复审线到期后预算本身未重新收口");

        Assert.True(
            LeanCacheBudgetPolicy.MinimumConfigurableBudgetSeconds
                < LeanCacheBudgetPolicy.DefaultProvisionBudgetSeconds);
    }

    [Fact]
    public void PolicyOverrideDeclarationReportsEveryRequiredItem()
    {
        var file = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "StrataLint.Cli", "Runtime", "LeanCacheBudgetPolicy.cs"));

        var constantIndex = file.IndexOf("internal const int DefaultProvisionBudgetSeconds", StringComparison.Ordinal);
        Assert.True(constantIndex > 0, "DefaultProvisionBudgetSeconds declaration not found");
        var head = file[..constantIndex];
        var summaryStart = head.LastIndexOf("/// <summary>", StringComparison.Ordinal);
        Assert.True(summaryStart >= 0, "DefaultProvisionBudgetSeconds has no <summary> block");
        var declaration = head[summaryStart..];

        foreach (var (label, pattern) in new[]
        {
            ("型别", @"\*\*分类:`policy-override`。\*\*"),
            ("非派生", @"「这不是派生值。」"),
            ("修订日期", @"\*\*日期\*\*:2026-08-30"),
            ("首次日期", @"首次收口 2026-08-25"),
            ("修订记录", @"\*\*修订记录\(2026-08-30\)\*\*"),
            ("域", @"\*\*域\*\*:"),
            ("正读数", @"\*\*正读数\*\*:"),
            ("负读数", @"\*\*负读数\*\*:"),
            ("永久案号(首次)", @"\*\*永久案号\*\*:https://github\.com/the-omega-institute/trureturing/issues/2535"),
            ("永久案号(修订)", @"→ https://github\.com/the-omega-institute/trureturing/issues/4120"),
            ("owner", @"\*\*owner\*\*:"),
            ("退出条件", @"\*\*退出条件 / 复审触发\*\*"),
            ("非永久", @"\*\*非永久\*\*:"),
        })
        {
            Assert.True(
                System.Text.RegularExpressions.Regex.IsMatch(declaration, pattern),
                $"policy-override 声明缺项或标签不符:{label}(pattern {pattern})");
        }
    }

    [Fact]
    public void ConfiguredBudgetAppliesToEveryProvisioningProcess()
    {
        if (OperatingSystem.IsWindows()) return;
        WithBudget("5400", () =>
        {
            using var fixture = new SharedLakeFixture();
            var runner = new BudgetRunner();
            var result = WorktreeCommand.Run(fixture.Reader, ["with-cache-reader", "--", "lake", "build"], runner);
            Assert.True(result.Success, result.Error);
            Assert.NotEmpty(runner.Budgets);
            Assert.All(runner.Budgets, budget => Assert.Equal(5400, budget.TotalSeconds));
        });
    }

    [Theory]
    [InlineData("1", 300)]
    [InlineData("30000", 21600)]
    public void ConfiguredBudgetUsesInvariantParsingAndClamps(string raw, int expectedSeconds)
    {
        AssertCacheGetBudget(raw, expectedSeconds);
    }

    [Fact]
    public void UnparseableBudgetFallsBackToTheCeiling()
    {
        WithBudget("invalid", () =>
            Assert.Equal(
                PinnedProductionBudgets.LeanCacheProvisionBudget,
                LeanCacheProvisioner.LeanCommandBudget));
    }
}
