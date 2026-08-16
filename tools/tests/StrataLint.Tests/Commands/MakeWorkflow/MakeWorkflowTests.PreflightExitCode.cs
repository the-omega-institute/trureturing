using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Theory]
    [InlineData("pass", 0)]
    [InlineData("semantic-test", 41)]
    [InlineData("semantic-gate", 42)]
    [InlineData("configuration", 78)]
    [InlineData("toolchain-missing", 127)]
    [InlineData("timeout", 124)]
    [InlineData("signal-term", 143)]
    [InlineData("exit-126", 126)]
    [InlineData("exit-127", 127)]
    [InlineData("unknown-dotnet", 73)]
    [InlineData("unknown", 73)]
    [InlineData("starved-lean-slot", 2)]
    public void PreflightPreservesExitCode(
        string scenario,
        int expectedExitCode)
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightScenario(scenario);

        Assert.Equal(expectedExitCode, result.ExitCode);
    }

    [Fact]
    public void PreflightRejectsStaleValues()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightScenario("stale-values");

        // The stale-values shim exits 44 from `emit-values --check`; scribe-content-checks.sh
        // runs under `set -e`, so preflight must surface exactly that code.
        Assert.Equal(44, result.ExitCode);
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
            if [[ -n "${PREFLIGHT_SCENARIO:-}" && "$#" -eq 6 \
              && "${1:-}" == diff && "${2:-}" == --name-only \
              && "${3:-}" == --no-renames && "${4:-}" == -z && "${6:-}" == -- ]]; then
              if [[ "$PREFLIGHT_SCENARIO" == stale-values ]]; then
                printf '%s\0' 'Golden/values-kernels.toml'
              else
                printf '%s\0' 'CLAUDE.md'
              fi
              exit 0
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
