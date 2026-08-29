using StrataLint.Engine;
using System.Text.RegularExpressions;

namespace StrataLint.Tests;

public sealed partial class EngineeringScopeHarnessTests
{

    private static ProcessOutput RunEngineeringScope(
        string engineeringRoot,
        string repositoryRoot,
        string planFile,
        string head,
        string @base,
        params string[] environment) =>
        RunEngineeringScopeMode(engineeringRoot, repositoryRoot, planFile, head, @base, "execute", environment);

    private static ProcessOutput RunEngineeringScopeMode(
        string engineeringRoot,
        string repositoryRoot,
        string planFile,
        string head,
        string @base,
        string mode,
        params string[] environment)
    {
        var project = Path.Combine(
            engineeringRoot,
            "tools",
            "StrataLint.EngineeringScope",
            "StrataLint.EngineeringScope.csproj");
        var build = TestProcessRunner.Run(
            DotnetHost(engineeringRoot),
            ["build", project, "--configuration", "Release", "--no-restore", "--nologo"],
            engineeringRoot,
            TestBudgets.LeanProcessHangGuard,
            2 * 1024 * 1024);
        Assert.True(
            build.ExitCode == 0,
            System.Text.Encoding.UTF8.GetString(build.StandardOutput)
                + System.Text.Encoding.UTF8.GetString(build.StandardError));
        var arguments = new List<string>(environment)
        {
            DotnetHost(engineeringRoot),
            "run",
            "--project",
            project,
            "--configuration",
            "Release",
            "--no-launch-profile",
            "--no-build",
            "--no-restore",
            "--",
            "--mode",
            mode,
            "--repository",
            repositoryRoot,
            "--head",
            head,
            "--base",
            @base,
            "--plan-file",
            planFile,
        };
        return TestProcessRunner.Run(
            "env",
            arguments,
            repositoryRoot,
            TestBudgets.LeanProcessHangGuard,
            2 * 1024 * 1024);
    }

    private static string DotnetHost(string root)
    {
        var result = TestProcessRunner.Run(
            "/bin/sh",
            ["-c", "command -v dotnet"],
            root,
            TestBudgets.ScriptProcessHangGuard,
            4096);
        Assert.Equal(0, result.ExitCode);
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static string GitText(string repository, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "git",
            ["-C", repository, .. arguments],
            repository,
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);
        Assert.Equal(0, result.ExitCode);
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static void Git(string repository, params string[] arguments) =>
        _ = GitText(repository, arguments);

    private static string ReadTemporaryText(string path)
    {
        using var reader = new StreamReader(path);
        return reader.ReadToEnd();
    }

}

public sealed class CandidateEngineeringReachabilityTests
{

}
