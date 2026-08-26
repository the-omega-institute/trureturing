using System.Reflection;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class BoundedProcessRunnerBudgetTests
{
    [Fact]
    public void TrackedTestDurationsHaveOneAnnotatedSource()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var durationFactory = string.Concat("TimeSpan", ".From");
        const string budgetPath = "tools/tests/StrataLint.Tests/TestBudgets.cs";
        var occurrences = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .SelectMany(file => File.ReadLines(file.FullPath)
                .Select((line, index) => (file.RelativePath, Line: index + 1, Text: line)))
            .Where(site => site.Text.Contains(durationFactory, StringComparison.Ordinal))
            .Where(site => site.RelativePath != budgetPath
                || (!site.Text.Contains("pinned-production-constant", StringComparison.Ordinal)
                    && !site.Text.Contains("infrastructure-hang-guard", StringComparison.Ordinal)))
            .Select(static site => $"{site.RelativePath}:{site.Line}")
            .ToArray();

        Assert.Empty(occurrences);
    }

    [Fact]
    public void TestScratchWallClockBridgeHasOneExactLocationPerCapability()
    {
        const string bridgePath = "tools/tests/StrataLint.Tests/TestScratchRoot.cs";
        var repositoryRoot = RepositoryLayout.FindRoot();
        var systemUtcNow = string.Concat("TimeProvider.System", ".GetUtcNow()");
        var retryWait = string.Concat("retryPause", ".Wait(25)");
        var sources = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Select(file => (file.RelativePath, Content: File.ReadAllText(file.FullPath)))
            .ToArray();
        var utcNow = sources
            .Where(source => source.Content.Contains(systemUtcNow, StringComparison.Ordinal))
            .Select(static source => source.RelativePath)
            .ToArray();
        var retryPause = sources
            .Where(source => source.Content.Contains(retryWait, StringComparison.Ordinal))
            .Select(static source => source.RelativePath)
            .ToArray();
        var bridge = Assert.Single(sources, static source => source.RelativePath == bridgePath).Content;

        Assert.Equal([bridgePath], utcNow);
        Assert.Equal([bridgePath], retryPause);
        Assert.Contains("internal static class TestEnvironmentBridge", bridge, StringComparison.Ordinal);
        Assert.Contains("internal static DateTime UtcNow()", bridge, StringComparison.Ordinal);
        Assert.Contains("internal static void PauseBeforeCleanupRetry()", bridge, StringComparison.Ordinal);
    }

    [Fact]
    public void HangDetectionBudgetAllowsFiveMinutesBeforeDeclaringSubprocessHung()
    {
        var field = typeof(BoundedProcessRunner).GetField(
            "HangDetectionBudget",
            BindingFlags.NonPublic | BindingFlags.Static);

        Assert.NotNull(field);
        Assert.Equal(
            TestBudgets.BoundedProcessRunnerBudget,
            Assert.IsType<TimeSpan>(field.GetValue(null)));
    }

}
