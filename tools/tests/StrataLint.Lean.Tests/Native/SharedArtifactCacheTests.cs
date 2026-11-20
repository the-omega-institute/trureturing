using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class SharedArtifactCacheTests
{
    [Fact]
    public void WarmDonorPublishesAndScopedBuildsReuseOnlyMatchingLocalArtifacts()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", Path.Combine(root,
                "tools/tests/StrataLint.Lean.Tests/Native/shared_artifact_cache.py")],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
