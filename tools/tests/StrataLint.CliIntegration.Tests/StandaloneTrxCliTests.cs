using System.Text;
using StrataLint.Cli;

namespace StrataLint.CliIntegration.Tests;

public sealed class StandaloneTrxCliTests
{
    [Theory]
    [InlineData("passed", 0, "TEST_ASSEMBLY_EVIDENCE_ACCEPTED")]
    [InlineData("hang-guard", 2, "INFRASTRUCTURE_UNRESOLVED")]
    [InlineData("wrong-assembly", 2, "required assembly")]
    [InlineData("missing", 2, "no TRX evidence")]
    public void StandaloneVerifierAcceptsPassedTestsAndRejectsInfrastructureSkips(string scenario, int expected, string diagnostic)
    {
        using var fixture = new TemporaryDirectory();
        if (scenario != "missing")
            File.WriteAllText(Path.Combine(fixture.Path, "run.trx"), $$"""
                <TestRun><Results><UnitTestResult testId="one" testName="Fixture.Runs" outcome="Passed" />
                {{(scenario == "hang-guard" ? "<UnitTestResult testId=\"two\" testName=\"Fixture.Hangs\" outcome=\"NotExecuted\"><Output><ErrorInfo><Message>infrastructure-hang-guard expired: fixture</Message></ErrorInfo></Output></UnitTestResult>" : "")}}
                </Results><TestDefinitions><UnitTest id="one" storage="Fixture.dll"><TestMethod className="Fixture" name="Runs" /></UnitTest>
                <UnitTest id="two" storage="Fixture.dll"><TestMethod className="Fixture" name="Hangs" /></UnitTest></TestDefinitions>
                <ResultSummary outcome="Completed"><Counters executed="1" passed="1" /></ResultSummary></TestRun>
                """);
        var result = TestProcessRunner.Run("dotnet", [typeof(Program).Assembly.Location, "verify-trx", "--results-directory", fixture.Path,
            "--required-assembly", scenario == "wrong-assembly" ? "Absent" : "Fixture"],
            fixture.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        var output = Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError);
        Assert.True(result.ExitCode == expected, $"expected {expected}, actual {result.ExitCode}: {output}");
        Assert.Contains(diagnostic, output, StringComparison.Ordinal);
        Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
    }
}
