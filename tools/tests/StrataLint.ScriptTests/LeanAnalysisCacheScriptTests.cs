using System.Text;

namespace StrataLint.Tests;

public sealed class LeanAnalysisCacheScriptTests
{
    [Theory]
    [InlineData("AnalysisCacheTests", "")]
    [InlineData("CurrentCacheTests", "actions")]
    [InlineData("CurrentCacheTests", "actions-corrupt")]
    [InlineData("CurrentCacheTests", "release")]
    [InlineData("CurrentCacheTests", "release-corrupt")]
    [InlineData("CurrentCacheTests", "miss")]
    [InlineData("CurrentCacheTests", "transport")]
    public void AnalysisPreparationAndProductionPreserveFailureBoundaries(string fixture, string seed)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("/usr/bin/env",
            [$"ANALYSIS_TEST_CLI={Path.Combine(AppContext.BaseDirectory, "StrataLint.dll")}",
                $"ANALYSIS_SEED_CASE={seed}",
                "python3", Path.Combine(root,
                    "tools/tests/StrataLint.ScriptTests/Fixtures/analysis_cache_contract.py"), fixture],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
