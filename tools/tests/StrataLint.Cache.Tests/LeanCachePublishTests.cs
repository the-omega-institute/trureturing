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
        var result = EngineeringProcess.Process(root, "python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/cache_snapshot_contract.py"), "SnapshotContracts"],
            hangGuard: TestBudgets.LongWorkflowProcessHangGuard, maximumOutputBytes: 1024 * 1024);
        Assert.True(result.Exit == 0,
            result.Text);
    }

}
