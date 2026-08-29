using System.Text;
using StrataLint.Engine;
using StrataLint.Tests;

namespace StrataLint.ArchitectureTests;

internal static class ProtectedBaseScriptSubjects
{
    internal static IReadOnlyList<string> Enumerate(string repositoryRoot)
    {
        var revision = ProtectedBaseRevision(repositoryRoot);
        var result = TestProcessRunner.Run(
            "git",
            ["ls-tree", "-r", "--name-only", revision, "--", "Makefile", "tools/Makefile", "tools/scripts"],
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget,
            1024 * 1024);
        Assert.Equal(0, result.ExitCode);

        return Encoding.UTF8.GetString(result.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Where(static path => path is "Makefile" or "tools/Makefile"
                || path.StartsWith("tools/scripts/", StringComparison.Ordinal)
                    && path.EndsWith(".sh", StringComparison.Ordinal))
            .Order(StringComparer.Ordinal)
            .ToArray();
    }

    private static string ProtectedBaseRevision(string repositoryRoot)
    {
        var explicitRevision = Environment.GetEnvironmentVariable("STRATALINT_PROTECTED_BASE");
        if (!string.IsNullOrWhiteSpace(explicitRevision))
        {
            return explicitRevision;
        }

        return string.Equals(
                Environment.GetEnvironmentVariable("GITHUB_EVENT_NAME"),
                "pull_request",
                StringComparison.Ordinal)
            ? "HEAD^1"
            : "HEAD";
    }
}
