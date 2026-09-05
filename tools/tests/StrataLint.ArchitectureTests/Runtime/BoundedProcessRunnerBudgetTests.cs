using System.Reflection;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

public sealed class BoundedProcessRunnerBudgetTests
{
    [Fact]
    public void ThirtySecondHangBudgetHasNoScatteredRepresentatives()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var oldRepresentative = string.Concat("TimeSpan.FromSeconds(", "30)");
        var occurrences = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => file.RelativePath.StartsWith("tools/", StringComparison.Ordinal)
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Where(static file => !IsBuildOutput(file.FullPath))
            .Select(file => (
                Path: file.RelativePath,
                Count: File.ReadLines(file.FullPath)
                    .Sum(line => CountOccurrences(line, oldRepresentative))))
            .Where(static site => site.Count > 0)
            .Select(static site => $"{site.Path}: {site.Count}")
            .ToArray();

        Assert.Empty(occurrences);
    }

    [Fact]
    public void TestScratchWallClockBridgeHasOneExactLocationPerCapability()
    {
        // TestScratchRoot.cs 随 L3c 迁入 StrataLint.TestSupport(#5419)。
        // **扫描面必须同时覆盖 tools/tests/ 与 tools/TestSupport/** —— 只改 bridgePath
        // 而不扩扫描面,该文件就落在扫描面之外,「全仓只有这一处可用挂钟」这条不变量
        // 会在新位置上静默失效(第 20 条:不得降级检测)。
        const string bridgePath = "tools/TestSupport/StrataLint.TestSupport/TestScratchRoot.cs";
        var repositoryRoot = RepositoryLayout.FindRoot();
        var systemUtcNow = string.Concat("TimeProvider.System", ".GetUtcNow()");
        var retryWait = string.Concat("retryPause", ".Wait(25)");
        var sources = GitIndexRepositoryFiles.Enumerate(repositoryRoot)
            .Where(static file => (file.RelativePath.StartsWith("tools/tests/", StringComparison.Ordinal)
                    || file.RelativePath.StartsWith("tools/TestSupport/", StringComparison.Ordinal))
                && file.RelativePath.EndsWith(".cs", StringComparison.Ordinal))
            .Select(file => (
                file.RelativePath,
                Content: string.Join('\n', File.ReadLines(file.FullPath))))
            .ToArray();
        var utcNow = sources
            .SelectMany(source => Enumerable.Repeat(
                source.RelativePath,
                CountOccurrences(source.Content, systemUtcNow)))
            .ToArray();
        var retryPause = sources
            .SelectMany(source => Enumerable.Repeat(
                source.RelativePath,
                CountOccurrences(source.Content, retryWait)))
            .ToArray();
        var bridge = Assert.Single(sources, static source => source.RelativePath == bridgePath).Content;

        Assert.Equal([bridgePath], utcNow);
        Assert.Equal([bridgePath], retryPause);
        Assert.Contains("internal static class TestEnvironmentBridge", bridge, StringComparison.Ordinal);
        Assert.Contains("internal static DateTime UtcNow()", bridge, StringComparison.Ordinal);
        Assert.Contains("internal static void PauseBeforeCleanupRetry()", bridge, StringComparison.Ordinal);
    }

    [Fact]
    public void HangDetectionBudgetIsFiniteAndPositive()
    {
        var field = typeof(BoundedProcessRunner).GetField(
            "HangDetectionBudget",
            BindingFlags.NonPublic | BindingFlags.Static);

        Assert.NotNull(field);
        var budget = Assert.IsType<TimeSpan>(field.GetValue(null));
        Assert.True(budget > TestBudgets.ZeroDuration);
        Assert.NotEqual(Timeout.InfiniteTimeSpan, budget);
    }

    private static bool IsBuildOutput(string path)
    {
        var segments = path.Split(Path.DirectorySeparatorChar);
        return segments.Contains("bin", StringComparer.Ordinal)
            || segments.Contains("obj", StringComparer.Ordinal);
    }

    private static int CountOccurrences(string content, string value)
    {
        var count = 0;
        var index = 0;
        while ((index = content.IndexOf(value, index, StringComparison.Ordinal)) >= 0)
        {
            count++;
            index += value.Length;
        }

        return count;
    }
}
