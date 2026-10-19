using System.Text;

namespace StrataLint.WorkflowScript.Tests;

public sealed class ResearchReadoutsScriptTests
{
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
