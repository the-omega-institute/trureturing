using System.Reflection;

namespace StrataLint.ArchitectureTests;

public sealed class BoundedProcessRunnerBudgetTests
{
    [Fact]
    public void ThirtySecondHangBudgetHasNoScatteredRepresentatives()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var toolsRoot = Path.Combine(repositoryRoot, "tools");
        var oldRepresentative = string.Concat("TimeSpan.FromSeconds(", "30)");
        var occurrences = Directory.EnumerateFiles(
                toolsRoot,
                "*.cs",
                SearchOption.AllDirectories)
            .Where(static path => !IsBuildOutput(path))
            .Select(path => (
                Path: Path.GetRelativePath(repositoryRoot, path),
                Count: CountOccurrences(File.ReadAllText(path), oldRepresentative)))
            .Where(static site => site.Count > 0)
            .Select(static site => $"{site.Path}: {site.Count}")
            .ToArray();

        Assert.Empty(occurrences);
    }

    [Fact]
    public void HangDetectionBudgetAllowsFiveMinutesBeforeDeclaringSubprocessHung()
    {
        var field = typeof(BoundedProcessRunner).GetField(
            "HangDetectionBudget",
            BindingFlags.NonPublic | BindingFlags.Static);

        Assert.NotNull(field);
        Assert.Equal(TimeSpan.FromMinutes(5), Assert.IsType<TimeSpan>(field.GetValue(null)));
    }

    private static bool IsBuildOutput(string path)
    {
        var segments = path.Split(Path.DirectorySeparatorChar);
        return segments.Contains("bin", StringComparer.Ordinal)
            || segments.Contains("obj", StringComparer.Ordinal);
    }

    private static int CountOccurrences(string source, string value) =>
        source.Split(value, StringSplitOptions.None).Length - 1;
}
