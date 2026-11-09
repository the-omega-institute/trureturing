using System.Text;
using System.Text.Json;
using StrataLint.Runtime;
using Xunit;
using Xunit.Abstractions;

namespace StrataLint.WorktreeContract.Tests;

public sealed class WorktreeProtocolTests(ITestOutputHelper output)
{
    private static readonly Lazy<string> BuiltCliRoot = new(BuildCli);

    private static string BuildCli()
    {
        var root = TestRepositoryLayout.FindRoot();
        var build = TestProcessRunner.Run("env", ["MSBUILDDISABLENODEREUSE=1",
            "DOTNET_CLI_USE_MSBUILD_SERVER=0", "UseSharedCompilation=false",
            "UseRazorBuildServer=false", "_RazorForceBuildServer=false", "make", "-C", "tools", "dotnet",
            "DOTNET_PROJECT=tools/StrataLint.Cli/StrataLint.Cli.csproj"], root,
            TimeSpan.FromSeconds(180), 1024 * 1024);
        Assert.True(build.ExitCode == 0,
            Encoding.UTF8.GetString(build.StandardOutput) + Encoding.UTF8.GetString(build.StandardError));
        return root;
    }

    public static IEnumerable<object[]> LifecycleCases()
    {
        if (OperatingSystem.IsWindows())
        {
            yield return ["unsupported-platform"];
            yield break;
        }
        var root = TestRepositoryLayout.FindRoot();
        var script = Path.Combine(root,
            "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/stale_lifecycle_cases.py");
        var result = TestProcessRunner.Run("python3", ["-B", script, root, "--list-tests"], root,
            TimeSpan.FromSeconds(120), 1024 * 1024);
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        var probes = JsonSerializer.Deserialize<string[]>(result.StandardOutput);
        Assert.NotNull(probes);
        Assert.NotEmpty(probes);
        Assert.Equal(probes.Length, probes.Distinct(StringComparer.Ordinal).Count());
        foreach (var probe in probes) yield return [probe];
    }

    [Theory]
    [MemberData(nameof(LifecycleCases))]
    public void DisposableGitLifecycleHonorsAgeAndNativeStalePolicy(string probe)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = BuiltCliRoot.Value;
        var script = Path.Combine(root,
            "tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/stale_lifecycle_cases.py");
        var result = TestProcessRunner.Run("python3", ["-B", script, root, probe], root,
            TimeSpan.FromSeconds(300), 1024 * 1024,
            interruptBeforeKill: TestProcessRunner.InterruptPythonFixture);
        output.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
        output.WriteLine(Encoding.UTF8.GetString(result.StandardError));
        Assert.True(result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("Ran 1 test", Encoding.UTF8.GetString(result.StandardError));
    }

    [Fact]
    public void AgentAttributionAndEntranceContractsRemainCovered()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = BuiltCliRoot.Value;
        foreach (var name in new[] { "agent_state_cases", "agent_state_entrance_cases" })
        {
            var script = Path.Combine(root,
                $"tools/tests/StrataLint.WorktreeContract.Tests/Fixtures/{name}.py");
            var result = TestProcessRunner.Run("python3", ["-B", script, root], root,
                TimeSpan.FromSeconds(300), 1024 * 1024);
            output.WriteLine(Encoding.UTF8.GetString(result.StandardOutput));
            output.WriteLine(Encoding.UTF8.GetString(result.StandardError));
            Assert.True(result.ExitCode == 0,
                Encoding.UTF8.GetString(result.StandardOutput) + Encoding.UTF8.GetString(result.StandardError));
        }
    }
}
