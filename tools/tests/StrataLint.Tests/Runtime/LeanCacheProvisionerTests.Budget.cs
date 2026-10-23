using StrataLint.Cli;

namespace StrataLint.Tests;

public sealed partial class LeanCacheProvisionerTests
{
    private const string BudgetVariable = "STRATALINT_LEAN_CACHE_TIMEOUT_SECONDS";

    [Theory]
    [InlineData(null, 21600)]
    [InlineData("invalid", 21600)]
    [InlineData("5400", 5400)]
    [InlineData("1", 300)]
    [InlineData("300", 300)]
    [InlineData("21600", 21600)]
    [InlineData("30000", 21600)]
    public void DependencyFetchReceivesTheBoundedCommandCutoff(string? raw, int expectedSeconds) =>
        AssertCacheGetBudget(raw, expectedSeconds);

    [Fact]
    public void PolicyOverrideDeclarationReportsSelectedScopeAndEvidenceBoundaries()
    {
        var file = File.ReadAllText(Path.Combine(
            TestRepositoryLayout.FindRoot(),
            "tools", "StrataLint.Lean", "Lean", "LeanCacheBudgetPolicy.cs"));
        var constantIndex = file.IndexOf("internal const int DefaultProvisionBudgetSeconds", StringComparison.Ordinal);
        Assert.True(constantIndex > 0, "DefaultProvisionBudgetSeconds declaration not found");
        var head = file[..constantIndex];
        var summaryStart = head.LastIndexOf("/// <summary>", StringComparison.Ordinal);
        Assert.True(summaryStart >= 0, "DefaultProvisionBudgetSeconds has no <summary> block");
        var declaration = head[summaryStart..];

        foreach (var (label, pattern) in new[]
        {
            ("classification", @"\*\*分类:`policy-override`。\*\*"),
            ("not derived", @"「这不是派生值。」"),
            ("scope", @"\*\*域\*\*:LeanCommandBudget"),
            ("selected source", @"\*\*来源 / 当前选择\*\*:caller-selected minimal infrastructure hotfix"),
            ("historical provenance", @"\*\*历史来源\*\*:https://github\.com/the-omega-institute/trureturing/issues/2535"),
            ("revision provenance", @"https://github\.com/the-omega-institute/trureturing/issues/4120"),
            ("historical positive readings", @"\*\*历史正读数\*\*:"),
            ("historical negative readings", @"\*\*历史负读数\*\*:"),
            ("fresh evidence limit", @"\*\*新读数\*\*:no current full-cold timing or full-closure benchmark"),
            ("owner", @"\*\*owner\*\*:repository τ=0 owner"),
            ("real exits and review", @"\*\*退出条件 / 复审触发\*\*:actual wrapped nonzero and timeout exits remain failures"),
            ("not permanent", @"\*\*非永久\*\*:a reviewed operational cutoff"),
        })
        {
            Assert.True(
                System.Text.RegularExpressions.Regex.IsMatch(declaration, pattern),
                $"policy-override declaration missing {label} (pattern {pattern})");
        }
    }
}
