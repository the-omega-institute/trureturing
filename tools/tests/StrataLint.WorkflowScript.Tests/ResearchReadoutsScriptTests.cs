using System.Text;

namespace StrataLint.WorkflowScript.Tests;

public sealed class ResearchReadoutsScriptTests
{
    [Theory]
    [InlineData("0/4")]
    [InlineData("1/4")]
    [InlineData("2/4")]
    [InlineData("3/4")]
    public void AutonomousResearchRoundRunsBehavioralFaultsThroughCanonicalMakeEntry(string shard)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("make",
            ["--no-print-directory", "-C", "tools", "autonomous-research-round-test", "ROUND_TEST_SHARD=" + shard],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void CompiledDependencyProtocolRunsThroughCanonicalMakeEntry()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("make",
            ["--no-print-directory", "-C", "tools", "compiled-dependencies-test"],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void ResearchReadoutsContractRunsThroughCanonicalMakeEntry()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("make",
            ["--no-print-directory", "-C", "tools", "research-readouts-test"],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
    }
}
