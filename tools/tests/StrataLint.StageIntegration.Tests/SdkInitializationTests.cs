using StrataLint.EngineeringScope;
using StrataLint.TestSupport;
using Xunit;

namespace StrataLint.StageIntegration.Tests;

[Collection("StrataLint.StageIntegration.Tests process boundary")]
public sealed class SdkInitializationTests
{
    [Theory]
    [InlineData(0)]
    [InlineData(17)]
    public void FirstUseCompletesOnceBeforeParallelTestsAndFailureStopsExecution(int initializationExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ExecutionFixture();
        foreach (var assembly in new[] { "First", "Second" })
            fixture.WriteTrx(Path.Combine(fixture.Root, "build/templates", assembly), "Passed", assembly);
        var pipes = EngineeringProcess.Process(fixture.Root, "mkfifo", ["build/first-ready", "build/second-ready"]);
        Assert.True(pipes.Exit == 0, pipes.Text);
        fixture.Write("build/bin/dotnet", $$"""
            #!/bin/bash
            set -euo pipefail
            [[ "${CANDIDATE_SHA-unset}" == unset && "$CI" == true && "$DOTNET_CLI_UI_LANGUAGE" == en-US ]]
            echo "$1" >> build/invocations
            if [[ "$1" == help ]]; then
              [[ ! -e build/initialized ]]
              echo initialized > build/initialized
              echo SDK-initialization-diagnostic >&2
              exit {{initializationExit}}
            fi
            [[ "$1" == test && -f build/initialized ]]
            assembly="$(basename "$2" .dll)"
            while [[ "$1" != --results-directory ]]; do shift; done
            results="$2"
            # Both children must be active before either can finish. A serial
            # project runner fails the bounded read rather than passing slowly.
            exec 3<> build/first-ready
            exec 4<> build/second-ready
            if [[ "$assembly" == First ]]; then
              echo ready >&3
              read -r -t 10 token <&4
            else
              echo ready >&4
              read -r -t 10 token <&3
            fi
            [[ "$token" == ready ]]
            cp "build/templates/$assembly/execution.trx" "$results/execution.trx"
            """);
        var shim = Path.Combine(fixture.Root, "build/bin/dotnet");
        File.SetUnixFileMode(shim, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var executable = Path.Combine(Path.GetDirectoryName(typeof(Program).Assembly.Location)!, "StrataLint.EngineeringScope");
        var result = EngineeringProcess.Capture(fixture.Root, executable, ["--repository", fixture.Root],
            new Dictionary<string, string>
            {
                ["PATH"] = Path.GetDirectoryName(shim) + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
                ["CANDIDATE_SHA"] = "ambient-candidate",
            });
        Assert.True(result.Exit == initializationExit, result.StandardOutput + result.StandardError);
        Assert.Contains("SDK-initialization-diagnostic", result.StandardError, StringComparison.Ordinal);
        Assert.Contains($"ENGINEERING_TEST_SDK_INITIALIZATION raw_exit={initializationExit}", result.StandardOutput, StringComparison.Ordinal);
        Assert.Equal(initializationExit == 0 ? new[] { "help", "test", "test" } : ["help"],
            File.ReadAllLines(Path.Combine(fixture.Root, "build/invocations")));
        if (initializationExit == 0)
        {
            var tests = CommonExecutionEvidence.ValidateTests(fixture.Root);
            Assert.Equal(2, tests.Projects.Length);
            Assert.All(tests.Projects, project => Assert.Equal(1, project.Executed));
        }
        else
        {
            Assert.DoesNotContain("ENGINEERING_TEST_PROJECT ", result.StandardOutput, StringComparison.Ordinal);
            Assert.False(File.Exists(Path.Combine(fixture.Root, CommonExecutionEvidence.TestsPath)));
        }
    }
}
