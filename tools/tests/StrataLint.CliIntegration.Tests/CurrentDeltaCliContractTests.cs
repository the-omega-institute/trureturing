using System.Text;
using StrataLint.Cli;

namespace StrataLint.CliIntegration.Tests;

public sealed class CurrentDeltaCliContractTests
{
    [Theory]
    [InlineData("check-current", false)]
    [InlineData("check-delta", true)]
    public void StandaloneChecksRequireTheExplicitReportAndRejectStageArguments(string command, bool delta)
    {
        using var fixture = new TemporaryDirectory();
        List<string[]> scenarios = [ [], ["--common-current", "current.json"],
            ["--common-engineering", "engineering.json"], ["--build-round", "round.json"] ];
        if (delta) scenarios.Add(["--candidate-lean-report", "report.json"]);
        else scenarios.Add(["--protected-base", new string('a', 40), "--candidate-lean-report", "report.json"]);
        foreach (var arguments in scenarios)
        {
            var result = TestProcessRunner.Run("dotnet", [typeof(Program).Assembly.Location, command, .. arguments],
                fixture.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Equal(2, result.ExitCode);
            Assert.Contains("INFRASTRUCTURE_FAILURE", Encoding.UTF8.GetString(result.StandardError));
            Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
        }
    }

    [Fact]
    public void CurrentReadsAParentlessRemotelessRepositoryBeforeReportingMissingReport()
    {
        using var fixture = new TemporaryDirectory();
        void Git(params string[] args) => Assert.Equal(0, TestProcessRunner.Run("git", args, fixture.Path,
            TestBudgets.ScriptProcessHangGuard, 64 * 1024).ExitCode);
        File.WriteAllText(Path.Combine(fixture.Path, "README.md"), "fixture\n");
        Git("init", "-q"); Git("add", ".");
        Git("-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless");
        var result = TestProcessRunner.Run("dotnet", [typeof(Program).Assembly.Location, "check-current",
            "--candidate-lean-report", Path.Combine(fixture.Path, "absent-report.json")], fixture.Path,
            TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("absent-report.json", Encoding.UTF8.GetString(result.StandardError));
        Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
    }
}
