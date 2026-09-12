using System.Text;

namespace StrataLint.Tests;

public sealed class CurrentReportDiagnosticsScriptTests
{
    [Theory]
    [InlineData("test_phase_diagnostics_survive_failed_staging_without_becoming_report_evidence")]
    [InlineData("test_external_diagnostics_allow_successful_validated_publication")]
    public void ReportDiagnosticsRespectProductionOutcome(string behavior)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            [Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py"), "PairTests." + behavior],
            root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
