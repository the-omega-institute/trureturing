using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PrShepherdRecalculationTests
{
    private const string WatchFreshnessScriptPath =
        "Meta/StrataLint/StrataLint.Tests/Commands/PrShepherd/pr-shepherd-watch-freshness.sh";

    [Fact]
    public void WatchFreshnessShellRegressionPasses()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = FindRepositoryRoot();
        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [Path.Combine(root, WatchFreshnessScriptPath)],
            root,
            TimeSpan.FromSeconds(60),
            256 * 1024);

        var standardOutput = Encoding.UTF8.GetString(result.StandardOutput);
        var standardError = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(
            result.ExitCode == 0,
            $"watch freshness shell regression failed with exit {result.ExitCode}\nstdout:\n{standardOutput}\nstderr:\n{standardError}");
        Assert.Equal(
            "pr-shepherd watch freshness: 6 passed, 0 failed, 6 total\n",
            standardOutput);
        Assert.Empty(standardError);
    }
}
