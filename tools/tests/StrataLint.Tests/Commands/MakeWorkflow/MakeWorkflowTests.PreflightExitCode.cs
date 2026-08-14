using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Theory]
    [InlineData("pass", 0, "PASS:NONE")]
    [InlineData("semantic-test", 41, "FAIL:SEMANTIC")]
    [InlineData("semantic-gate", 42, "FAIL:SEMANTIC")]
    [InlineData("configuration", 78, "FAIL:CONFIGURATION")]
    [InlineData("toolchain-missing", 127, "FAIL:TOOLCHAIN")]
    [InlineData("timeout", 124, "FAIL:INFRASTRUCTURE")]
    [InlineData("signal-term", 143, "FAIL:INFRASTRUCTURE")]
    [InlineData("exit-126", 126, "FAIL:TOOLCHAIN")]
    [InlineData("exit-127", 127, "FAIL:TOOLCHAIN")]
    [InlineData("unknown-dotnet", 73, "UNKNOWN:UNKNOWN")]
    [InlineData("unknown", 73, "UNKNOWN:UNKNOWN")]
    [InlineData("starved-lean-slot", 2, "UNKNOWN:UNKNOWN")]
    public void PreflightPreservesExitCode(
        string scenario,
        int expectedExitCode,
        string expectedDeclaration)
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightScenario(scenario);

        Assert.Equal(expectedExitCode, result.ExitCode);
        Assert.EndsWith(
            $"FKST_LOCAL_ITERATION_RESULT:v2:{expectedDeclaration}\n",
            System.Text.Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void PreflightRejectsStaleValuesBeforeDeclaringPass()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightScenario("stale-values");
        var output = System.Text.Encoding.UTF8.GetString(result.StandardOutput);

        Assert.NotEqual(0, result.ExitCode);
        Assert.DoesNotContain(
            "FKST_LOCAL_ITERATION_RESULT:v2:PASS:NONE",
            output,
            StringComparison.Ordinal);
        Assert.EndsWith(
            "FKST_LOCAL_ITERATION_RESULT:v2:FAIL:SEMANTIC\n",
            output,
            StringComparison.Ordinal);
    }

    /// <summary>
    /// Stands in for the artifact a real <c>make lean-report</c> leaves behind, and removes it
    /// again only when this fixture is the one that put it there.
    /// </summary>
    private sealed class ScenarioLeanReport : IDisposable
    {
        private readonly string path;
        private readonly bool created;

        internal ScenarioLeanReport(string repositoryRoot)
        {
            path = Path.Combine(repositoryRoot, ".lake", "build", "stratalint", "raw-lean-report.json");
            if (File.Exists(path))
            {
                return;
            }

            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, "{}\n");
            created = true;
        }

        public void Dispose()
        {
            if (created && File.Exists(path))
            {
                File.Delete(path);
            }
        }
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static ProcessOutput RunPreflightScenario(string scenario)
    {
        var root = TestRepositoryLayout.FindRoot();
        // The stub `make lean-report` claims success without writing anything, so on a clean
        // checkout the report it is supposed to have produced does not exist and the content
        // checks fail closed on a missing report rather than on the scenario under test. A
        // successful lean-report produces a report; the stub has to be honest about that.
        // Only a report this fixture created is removed, so a real one is never clobbered.
        using var report = new ScenarioLeanReport(root);
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        Directory.CreateDirectory(binDirectory);
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            """
            #!/usr/bin/env bash
            if [[ "${PREFLIGHT_SCENARIO:-}" == configuration && "$*" == "rev-parse --show-toplevel" ]]; then
              exit 78
            fi
            exec /usr/bin/git "$@"
            """);
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            if [[ "${1:-}" == --version ]]; then
              [[ "${PREFLIGHT_SCENARIO:-}" != toolchain-missing ]] || exit 127
              exit 0
            fi
            if [[ "${PREFLIGHT_SCENARIO:-}" == stale-values && "$*" == *"emit-values --check"* ]]; then
              printf '%s\n' 'out of date: Evidence/D5/values.json' >&2
              exit 44
            fi
            if [[ "${1:-}" == build ]]; then exit 1; fi
            if [[ "${1:-}" == msbuild ]]; then exit 1; fi
            exit 0
            """);
        WriteExecutable(
            Path.Combine(binDirectory, "lake"),
            """
            #!/usr/bin/env bash
            [[ "${1:-}" == --version ]] || exit 64
            exit 0
            """);
        WriteExecutable(
            Path.Combine(binDirectory, "make"),
            """
            #!/usr/bin/env bash
            directory="."
            target=""
            while [[ $# -gt 0 ]]; do
              case "$1" in
                -C)
                  [[ $# -ge 2 ]] || exit 64
                  directory="$2"
                  shift 2
                  ;;
                *)
                  target="$1"
                  break
                  ;;
              esac
            done
            case "${PREFLIGHT_SCENARIO:-}:$directory:$target" in
              semantic-test:tools:test) exit 41 ;;
              semantic-gate:.:gate) exit 42 ;;
              timeout:.:lean-report) exit 124 ;;
              signal-term:.:lean-report) kill -TERM "$PPID"; exit 0 ;;
              exit-126:.:lean-report) exit 126 ;;
              exit-127:.:lean-report) exit 127 ;;
              unknown-dotnet:tools:dotnet) exit 73 ;;
              unknown:.:lean-report) exit 73 ;;
              starved-lean-slot:.:lean-report) exit 2 ;;
            esac
            exit 0
            """);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PREFLIGHT_SCENARIO=\"$1\" BASE=HEAD^ PATH=\"$2:/usr/bin:/bin\" exec /bin/bash \"$3\"",
                "preflight-contract",
                scenario,
                binDirectory,
                Path.Combine(root, PreflightScriptPath),
            ],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        return result;
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteExecutable(string path, string content)
    {
        File.WriteAllText(path, content + "\n");
        File.SetUnixFileMode(
            path,
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
