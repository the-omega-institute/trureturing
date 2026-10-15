using StrataLint.TestSupport;
using Xunit;
using TheoryAttribute = Xunit.SkippableTheoryAttribute;

namespace StrataLint.Cache.Release.Tests;

public sealed class LeanCachePublishTests
{
    [Theory]
    [MemberData(nameof(ReleaseCases))]
    public void ReleaseSeedsUsePartitionAndAtomicPublication(string testName)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = EngineeringProcess.Process(root, "python3", ["-B",
            Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py"), testName],
            hangGuard: TestBudgets.LongWorkflowProcessHangGuard, maximumOutputBytes: 1024 * 1024);
        Assert.True(result.Exit == 0,
            result.Text);
    }

    public static IEnumerable<object[]> ReleaseCases()
    {
        var root = TestRepositoryLayout.FindRoot();
        var fixture = Path.Combine(root, "tools/tests/StrataLint.ScriptTests/Fixtures/lean_seed_contract.py");
        var result = EngineeringProcess.Process(root, "python3", ["-B", fixture, "--list"],
            hangGuard: TestBudgets.ScriptProcessHangGuard, maximumOutputBytes: 1024 * 1024);
        if (result.Exit != 0)
            throw new InvalidOperationException("Release fixture case discovery failed:\n" + result.Text);

        foreach (var name in result.Text.Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries))
            yield return ["TransportTests." + name];
    }
}
