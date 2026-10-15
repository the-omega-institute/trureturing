using StrataLint.TestSupport;
using Xunit;
using TheoryAttribute = Xunit.SkippableTheoryAttribute;

namespace StrataLint.Cache.Release.Tests;

public sealed class LeanCachePublishTests
{
    [Theory]
    [InlineData("transport_suite")]
    [InlineData("verification_suite")]
    [InlineData("local_suite")]
    public void ReleaseSeedsUsePartitionAndAtomicPublication(string suite)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = EngineeringProcess.Process(root, "python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py"), suite],
            hangGuard: TestBudgets.LongWorkflowProcessHangGuard, maximumOutputBytes: 1024 * 1024);
        Assert.True(result.Exit == 0,
            result.Text);
    }
}
