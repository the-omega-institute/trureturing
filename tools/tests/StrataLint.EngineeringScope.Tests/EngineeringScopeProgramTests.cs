using System.Diagnostics;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.EngineeringScope.Tests;

[Collection("Engineering scope process boundary")]
public sealed class EngineeringScopeProgramTests
{
    [Theory]
    [InlineData(true, true, 0, false)]
    [InlineData(true, true, 0, true)]
    [InlineData(true, false, 1, false)]
    [InlineData(false, true, 1, false)]
    public void CurrentRunnerExecutesPrebuiltTestsAndNeverRetries(bool prebuild, bool passes, int expected, bool all)
    {
        var root = TemporaryFileSystem.Directory.CreateTempSubdirectory("engineering-process-").FullName;
        try
        {
            const string project = "tools/tests/Probe/Probe.csproj";
            var directory = Path.Combine(root, "tools/tests/Probe");
            TemporaryFileSystem.Directory.CreateDirectory(directory);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, ".gitignore"), ".lake/\nbuild/\nbin/\nobj/\n");
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, project), """
                <Project Sdk="Microsoft.NET.Sdk">
                  <PropertyGroup><TargetFramework>net10.0</TargetFramework><IsTestProject>true</IsTestProject></PropertyGroup>
                  <ItemGroup>
                    <PackageReference Include="Microsoft.NET.Test.Sdk" Version="18.0.1" />
                    <PackageReference Include="xunit" Version="2.9.3" />
                    <PackageReference Include="xunit.runner.visualstudio" Version="3.1.4" />
                  </ItemGroup>
                </Project>
                """);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(directory, "Probe.cs"),
                "using Xunit; public sealed class Probe { [Fact] public void Runs() { Assert.True(" + (passes ? "true" : "false") + "); } }");
            var retiredSuite = Path.Combine(root, "tools/tests/StrataLint.ScriptTests");
            TemporaryFileSystem.Directory.CreateDirectory(retiredSuite);
            TemporaryFileSystem.File.WriteAllText(Path.Combine(retiredSuite, "StrataLint.ScriptTests.csproj"),
                "<Project><PropertyGroup><IsTestProject>true</IsTestProject></PropertyGroup></Project>");
            TemporaryFileSystem.Directory.CreateDirectory(Path.Combine(root, "Meta"));
            TemporaryFileSystem.File.WriteAllText(Path.Combine(root, EngineeringRegistrationFixture.Path),
                EngineeringRegistrationFixture.Manifest(
                    new EngineeringProjectFixture("tools/tests/Probe/Probe.csproj", "Probe", "cross-cutting-test", true, ["tools/tests/Probe/**/*.cs"]),
                    new EngineeringProjectFixture("tools/tests/StrataLint.ScriptTests/StrataLint.ScriptTests.csproj", "StrataLint.ScriptTests", "cross-cutting-test", false, [])));
            Run(root, "git", ["init", "-q"]);
            Run(root, "git", ["add", "."]);
            Run(root, "git", ["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "commit", "-qm", "parentless"]);
            if (prebuild) Run(root, "dotnet", ["build", project, "--configuration", "Release", "--nologo"]);
            using var output = new StringWriter();
            using var error = new StringWriter();
            var exit = Program.Run(["--repository", root, .. all ? new[] { "--all" } : []], TestResultEvidence.Load, output, error);
            Assert.True(exit == expected, output + "\n" + error);
            Assert.Single(output.ToString().Split('\n'), line => line.StartsWith("ENGINEERING_TEST_PROJECT ", StringComparison.Ordinal));
            Assert.DoesNotContain("ENGINEERING_TEST_RETRY", output.ToString(), StringComparison.Ordinal);
            Assert.True(TemporaryFileSystem.File.Exists(Path.Combine(root, CommonExecutionEvidence.TestsPath)));
            if (expected == 0) CommonExecutionEvidence.ValidateTests(root);
        }
        finally { TemporaryFileSystem.Directory.Delete(root, recursive: true); }
    }

    [Fact]
    public void CandidateTestInvocationIsPrebuiltWithMinimalVerbosity()
    {
        var arguments = Program.BuildTestArguments("tools/tests/Probe/Probe.csproj", "/tmp/results");
        Assert.Contains("--no-build", arguments);
        Assert.Contains("--no-restore", arguments);
        Assert.Equal("minimal", arguments[Array.IndexOf(arguments.ToArray(), "--verbosity") + 1]);
    }

    [Theory]
    [InlineData("--base")]
    [InlineData("--head")]
    [InlineData("--full")]
    public void ExplicitAllRejectsHistoricalSelectionOptions(string option)
    {
        using var output = new StringWriter();
        using var error = new StringWriter();
        var exit = Program.Run(["--repository", "/missing-repository", "--all", option, "value"],
            TestResultEvidence.Load, output, error);
        Assert.Equal(2, exit);
        Assert.Contains("options must be", error.ToString(), StringComparison.Ordinal);
        Assert.Empty(output.ToString());
    }

    private static void Run(string root, string command, string[] arguments)
    {
        var start = new ProcessStartInfo(command) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true };
        foreach (var argument in arguments) start.ArgumentList.Add(argument);
        using var process = Process.Start(start)!;
        var stdout = process.StandardOutput.ReadToEndAsync();
        var stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult());
    }
}

[CollectionDefinition("Engineering scope process boundary", DisableParallelization = true)]
public sealed class EngineeringScopeProcessBoundaryCollection;
