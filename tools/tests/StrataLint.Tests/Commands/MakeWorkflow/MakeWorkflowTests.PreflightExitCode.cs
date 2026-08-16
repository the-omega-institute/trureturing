using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void PreflightScenarioLeavesTheSourceTreeAndItsCanonicalReportUntouched()
    {
        if (OperatingSystem.IsWindows()) return;

        var canonicalSource = TestRepositoryLayout.FindRoot();
        using var source = new TemporaryDirectory();
        foreach (var relativePath in new[]
        {
            PreflightScriptPath,
            "tools/scripts/perf-event-lib.sh",
            ScribeContentChecksScriptPath,
        })
        {
            var destination = Path.Combine(source.Path, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(Path.Combine(canonicalSource, relativePath), destination);
        }
        var sourceReport = Path.Combine(
            source.Path,
            ".lake",
            "build",
            "stratalint",
            "raw-lean-report.json");
        Directory.CreateDirectory(Path.GetDirectoryName(sourceReport)!);
        var sentinel = System.Text.Encoding.UTF8.GetBytes(
            "canonical-source-report-sentinel: byte-distinct and not a fixture report\n");
        File.WriteAllBytes(sourceReport, sentinel);
        File.WriteAllText(Path.Combine(source.Path, "README.md"), "synthetic source\n");
        RunScenarioGit(source.Path, "init", "--initial-branch=dev");
        RunScenarioGit(source.Path, "config", "user.email", "preflight@example.invalid");
        RunScenarioGit(source.Path, "config", "user.name", "Preflight Fixture");
        RunScenarioGit(source.Path, "add", ".");
        RunScenarioGit(source.Path, "commit", "-m", "synthetic source baseline");
        var headBefore = RunScenarioGitForOutput(source.Path, "rev-parse", "HEAD");
        var statusBefore = RunScenarioGitForOutput(
            source.Path,
            "status",
            "--porcelain=v1",
            "--untracked-files=all");
        var sourceReportBlobBefore = RunScenarioGitForOutput(
            source.Path,
            "hash-object",
            sourceReport);

        var result = RunPreflightScenario("pass", source.Path);

        Assert.Equal(
            sourceReportBlobBefore,
            RunScenarioGitForOutput(source.Path, "hash-object", sourceReport));
        Assert.Equal(headBefore, RunScenarioGitForOutput(source.Path, "rev-parse", "HEAD"));
        Assert.Equal(
            statusBefore,
            RunScenarioGitForOutput(
                source.Path,
                "status",
                "--porcelain=v1",
                "--untracked-files=all"));
        Assert.Equal(0, result.ExitCode);
    }

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

        var result = RunPreflightScenario(scenario, TestRepositoryLayout.FindRoot());

        Assert.Equal(expectedExitCode, result.ExitCode);
    }

    [Fact]
    public void PreflightRejectsStaleValues()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightScenario("stale-values", TestRepositoryLayout.FindRoot());

        // The stale-values shim exits 44 from `emit-values --check`; scribe-content-checks.sh
        // runs under `set -e`, so preflight must surface exactly that code.
        Assert.Equal(44, result.ExitCode);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static ProcessOutput RunPreflightScenario(string scenario, string sourceRoot)
    {
        using var fixture = new TemporaryDirectory();
        var root = Path.Combine(fixture.Path, "candidate");
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var preflight = Path.Combine(root, PreflightScriptPath);
        var perfEvents = Path.Combine(root, "tools", "scripts", "perf-event-lib.sh");
        var scribeChecks = Path.Combine(root, ScribeContentChecksScriptPath);
        var report = Path.Combine(root, ".lake", "build", "stratalint", "raw-lean-report.json");
        Directory.CreateDirectory(Path.GetDirectoryName(preflight)!);
        Directory.CreateDirectory(Path.GetDirectoryName(scribeChecks)!);
        Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        Directory.CreateDirectory(binDirectory);
        File.Copy(Path.Combine(sourceRoot, PreflightScriptPath), preflight);
        File.Copy(Path.Combine(sourceRoot, "tools/scripts/perf-event-lib.sh"), perfEvents);
        File.Copy(Path.Combine(sourceRoot, ScribeContentChecksScriptPath), scribeChecks);
        File.WriteAllText(
            report,
            "{\"modules\":[],\"schema\":\"stratalint-raw-lean-report-v1\"}\n");
        File.WriteAllText(Path.Combine(root, "README.md"), "base\n");
        RunScenarioGit(root, "init", "--initial-branch=dev");
        RunScenarioGit(root, "config", "user.email", "preflight@example.invalid");
        RunScenarioGit(root, "config", "user.name", "Preflight Fixture");
        RunScenarioGit(root, "add", "README.md", "tools");
        RunScenarioGit(root, "commit", "-m", "fixture base");
        File.AppendAllText(Path.Combine(root, "README.md"), "candidate\n");
        RunScenarioGit(root, "add", "README.md");
        RunScenarioGit(root, "commit", "-m", "fixture candidate");
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
                preflight,
            ],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        return result;
    }

    private static void RunScenarioGit(string root, params string[] arguments)
    {
        var result = BoundedProcessRunner.Run(
            "/usr/bin/git",
            arguments,
            root,
            TimeSpan.FromSeconds(10),
            64 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                System.Text.Encoding.UTF8.GetString(result.StandardError));
        }
    }

    private static string RunScenarioGitForOutput(string root, params string[] arguments)
    {
        var result = BoundedProcessRunner.Run(
            "/usr/bin/git",
            arguments,
            root,
            TimeSpan.FromSeconds(10),
            64 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                System.Text.Encoding.UTF8.GetString(result.StandardError));
        }
        return System.Text.Encoding.UTF8.GetString(result.StandardOutput);
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
