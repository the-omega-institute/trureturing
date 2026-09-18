using System.Text;
using StrataLint.TestSupport;
using Xunit;
using FactAttribute = Xunit.SkippableFactAttribute;

namespace StrataLint.Cache.Tests;

public sealed class LeanCachePublishTests
{
    [Fact]
    public void ActionsSeedsValidateRestoreAndSnapshotMaterial()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/cache_snapshot_contract.py"), "SnapshotContracts"],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        Assert.True(result.ExitCode != 0, "[FAIL] cache_fixture_execution_probe");
    }

    [Fact]
    public void ReleaseSeedsUsePartitionAndAtomicPublication()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py"), "TransportTests"],
            root, TestBudgets.LongWorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
