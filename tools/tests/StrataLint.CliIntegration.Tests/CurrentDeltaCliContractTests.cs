using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;
using StrataLint.EngineeringScope;
using StrataLint.TestSupport;

namespace StrataLint.CliIntegration.Tests;

public sealed class CurrentDeltaCliContractTests
{
    [Theory]
    [InlineData("check", "--artifact-capacity", "USAGE: StrataLint check [--protected-base REV] --candidate-lean-report FILE [--scribe-paths-from FILE]")]
    [InlineData("check-current", "--artifact-capacity", "USAGE: StrataLint check-current --candidate-lean-report FILE [--scribe-paths-from FILE]")]
    [InlineData("check-current", "--protected-base", "USAGE: StrataLint check-current --candidate-lean-report FILE [--scribe-paths-from FILE]")]
    [InlineData("check-delta", "--scribe-paths-from", "USAGE: StrataLint check-delta --protected-base REV [--candidate-lean-report FILE] [--artifact-capacity]")]
    public void UnsupportedCheckOptionsFailBeforeRepositoryAccess(
        string command, string option, string usage)
    {
        var gateway = EmptyGateway();
        var environment = new ProductionCliEnvironment(
            "/fixture", gateway, new FakeLeanReportSource(null));

        var result = command switch
        {
            "check" => Failure(environment.Check([option, "value", "--candidate-lean-report", "report.json"])),
            "check-current" => environment.CheckCurrent([option, "value", "--candidate-lean-report", "report.json"]),
            "check-delta" => environment.CheckDelta(["--protected-base", new string('a', 40), option, "value"]),
            _ => throw new ArgumentOutOfRangeException(nameof(command)),
        };

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(usage, result.Error, StringComparison.Ordinal);
        Assert.Equal(0, gateway.ReadCount);
        Assert.Equal(0, gateway.PrepareCount);

        static ExplicitCommandResult Failure(AdmissionOutcome outcome) => outcome switch
        {
            AdmissionOutcome.InfrastructureFailure failure => new(2, string.Empty, failure.Message),
            _ => throw new Xunit.Sdk.XunitException("expected infrastructure failure"),
        };
    }

    [Theory]
    [InlineData("check")]
    [InlineData("check-current")]
    [InlineData("check-delta")]
    public void DeclaredCheckOptionsAreParsedBeforeRepositoryWork(string command)
    {
        var gateway = EmptyGateway();
        var environment = new ProductionCliEnvironment(
            "/fixture", gateway, new FakeLeanReportSource(null));
        var arguments = command switch
        {
            "check" => (IReadOnlyList<string>)[
                "--protected-base", new string('a', 40),
                "--candidate-lean-report", "missing-report.json",
                "--scribe-paths-from", "missing-paths.txt"],
            "check-current" => (IReadOnlyList<string>)[
                "--candidate-lean-report", "missing-report.json",
                "--scribe-paths-from", "missing-paths.txt"],
            "check-delta" => (IReadOnlyList<string>)[
                "--protected-base", new string('a', 40),
                "--candidate-lean-report", "missing-report.json",
                "--artifact-capacity"],
            _ => throw new ArgumentOutOfRangeException(nameof(command)),
        };

        var result = command switch
        {
            "check" => Failure(environment.Check(arguments)),
            "check-current" => environment.CheckCurrent(arguments),
            "check-delta" => environment.CheckDelta(arguments),
            _ => throw new ArgumentOutOfRangeException(nameof(command)),
        };

        Assert.Equal(2, result.ExitCode);
        Assert.DoesNotContain("USAGE:", result.Error, StringComparison.Ordinal);
        Assert.True(gateway.ReadCount > 0 || gateway.PrepareCount > 0);

        static ExplicitCommandResult Failure(AdmissionOutcome outcome) => outcome switch
        {
            AdmissionOutcome.InfrastructureFailure failure => new(2, string.Empty, failure.Message),
            _ => throw new Xunit.Sdk.XunitException("expected infrastructure failure"),
        };
    }

    private static FakeRepositoryGateway EmptyGateway() => new(
        RawChangeSet.Create([]),
        RawRepositorySnapshot.Create([]),
        RawRepositorySnapshot.Create([]));

    [Theory]
    [InlineData("check", "USAGE: StrataLint check [--protected-base REV] --candidate-lean-report FILE [--scribe-paths-from FILE]")]
    [InlineData("check-current", "USAGE: StrataLint check-current --candidate-lean-report FILE [--scribe-paths-from FILE]")]
    public void StandaloneChecksRejectArtifactCapacityAsAnUnsupportedUsageOption(
        string command, string usage)
    {
        using var fixture = new TemporaryDirectory();
        var result = TestProcessRunner.Run("dotnet", [typeof(StrataLint.Cli.Program).Assembly.Location,
            command, "--artifact-capacity", "--candidate-lean-report", "report.json"], fixture.Path,
            TestBudgets.ScriptProcessHangGuard, 64 * 1024);

        Assert.Equal(2, result.ExitCode);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains(usage, error, StringComparison.Ordinal);
        Assert.DoesNotContain(usage + " [--artifact-capacity]", error,
            StringComparison.Ordinal);
    }

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
            var result = TestProcessRunner.Run("dotnet", [typeof(StrataLint.Cli.Program).Assembly.Location, command, .. arguments],
                fixture.Path, TestBudgets.ScriptProcessHangGuard, 64 * 1024);
            Assert.Equal(2, result.ExitCode);
            Assert.Contains("INFRASTRUCTURE_FAILURE", Encoding.UTF8.GetString(result.StandardError));
            Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
        }
    }

    [Fact]
    public void CliRuntimeConfigurationConservesGarbageCollectedMemory()
    {
        var path = Path.ChangeExtension(typeof(StrataLint.Cli.Program).Assembly.Location, ".runtimeconfig.json");
        using var document = System.Text.Json.JsonDocument.Parse(File.ReadAllBytes(path));
        var properties = document.RootElement.GetProperty("runtimeOptions").GetProperty("configProperties");
        Assert.Equal(9, properties.GetProperty("System.GC.ConserveMemory").GetInt32());
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
        var result = TestProcessRunner.Run("dotnet", [typeof(StrataLint.Cli.Program).Assembly.Location, "check-current",
            "--candidate-lean-report", Path.Combine(fixture.Path, "absent-report.json")], fixture.Path,
            TestBudgets.ScriptProcessHangGuard, 64 * 1024);
        Assert.Equal(2, result.ExitCode);
        Assert.Contains("absent-report.json", Encoding.UTF8.GetString(result.StandardError));
        Assert.False(Directory.Exists(Path.Combine(fixture.Path, "build/ci")));
    }
}
