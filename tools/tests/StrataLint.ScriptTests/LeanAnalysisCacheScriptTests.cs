using System.Text;

namespace StrataLint.Tests;

public sealed class LeanAnalysisCacheScriptTests
{
    [Fact]
    public void AnalysisPreparationAndProductionPreserveFailureBoundaries()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("/usr/bin/env",
            [$"ANALYSIS_TEST_PRODUCER={Path.Combine(AppContext.BaseDirectory, "StrataLint.Lean.dll")}",
                "python3", Path.Combine(root,
                    "tools/tests/StrataLint.ScriptTests/Fixtures/analysis_cache_contract.py"), "AnalysisCacheTests"],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
