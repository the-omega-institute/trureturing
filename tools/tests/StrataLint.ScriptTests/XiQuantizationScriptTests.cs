using System.Text;

namespace StrataLint.Tests;

public sealed class XiQuantizationScriptTests
{
    [Fact]
    public void ExactQuantizationScientificAccounting()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root, "tools/scripts/agent/test_xi_quantization.py")], root,
            TestBudgets.LeanProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
