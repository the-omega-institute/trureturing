using System.Text;
using System.Text.Json;

namespace StrataLint.WorkflowScript.Tests;

public sealed class ResearchReadoutsScriptTests
{
    public static IEnumerable<object[]> AutonomousResearchCases()
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("make",
            ["--no-print-directory", "-C", "tools", "autonomous-research-round-test", "ROUND_TEST_CASE=list"],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        var cases = JsonSerializer.Deserialize<string[]>(result.StandardOutput);
        Assert.NotNull(cases);
        Assert.NotEmpty(cases);
        Assert.Equal(cases.Length, cases.Distinct(StringComparer.Ordinal).Count());
        foreach (var testCase in cases) yield return [testCase];
    }

    [Theory]
    [MemberData(nameof(AutonomousResearchCases))]
    public void AutonomousResearchRoundRunsBehavioralFaultsThroughCanonicalMakeEntry(string testCase)
    {
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("make",
            ["--no-print-directory", "-C", "tools", "autonomous-research-round-test", "ROUND_TEST_CASE=" + testCase],
            root, TestBudgets.ScriptProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("Ran 1 test", Encoding.UTF8.GetString(result.StandardError));
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
