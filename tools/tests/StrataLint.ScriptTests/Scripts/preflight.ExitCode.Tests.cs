using StrataLint.Engine;

namespace StrataLint.ScriptTests;

public sealed partial class PreflightScriptTests
{
    [Fact]
    public void PreflightScenarioScriptClosureFollowsTheSourceDirectory()
    {
        using var source = new TemporaryDirectory();
        using var destination = new TemporaryDirectory();
        var futureScript = Path.Combine(
            source.Path,
            "tools",
            "scripts",
            "future",
            "arbitrary.sh");
        Directory.CreateDirectory(Path.GetDirectoryName(futureScript)!);
        File.WriteAllText(futureScript, "#!/usr/bin/env bash\n");

        CopyPreflightScriptClosure(source.Path, destination.Path);

        Assert.True(File.Exists(Path.Combine(
            destination.Path,
            "tools",
            "scripts",
            "future",
            "arbitrary.sh")));
    }

    [Fact]
    public void PreflightScenarioLeavesTheSourceTreeAndItsCanonicalReportUntouched()
    {
        if (OperatingSystem.IsWindows()) return;

        var canonicalSource = TestRepositoryLayout.FindRoot();
        using var source = new TemporaryDirectory();
        CopyPreflightScriptClosure(canonicalSource, source.Path);
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
    public void R15PreflightIgnoresStaleValuesProjection()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightScenario("stale-values", TestRepositoryLayout.FindRoot());

        // The shim still exits 44 if the deleted freshness ritual is invoked.
        Assert.Equal(0, result.ExitCode);
    }

    [Fact]
    public void BannedApiDiagnosticParityMismatchFailsPreflight()
    {
        if (OperatingSystem.IsWindows()) return;

        var result = RunPreflightScenario(
            "banned-api-diagnostic-mismatch",
            TestRepositoryLayout.FindRoot());

        Assert.Equal(1, result.ExitCode);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static ProcessOutput RunPreflightScenario(string scenario, string sourceRoot)
    {
        using var fixture = new TemporaryDirectory();
        var root = Path.Combine(fixture.Path, "candidate");
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var preflight = Path.Combine(root, PreflightScriptPath);
        var report = Path.Combine(root, ".lake", "build", "stratalint", "raw-lean-report.json");
        CopyPreflightScriptClosure(sourceRoot, root);
        CopyBannedApiCompileFailProof(root);
        Directory.CreateDirectory(Path.GetDirectoryName(report)!);
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(
            report,
            "{\"modules\":[],\"schema\":\"stratalint-raw-lean-report-v2\"}\n");
        File.WriteAllText(Path.Combine(root, "README.md"), "base\n");
        RunScenarioGit(root, "init", "--initial-branch=dev");
        RunScenarioGit(root, "config", "user.email", "preflight@example.invalid");
        RunScenarioGit(root, "config", "user.name", "Preflight Fixture");
        RunScenarioGit(root, "add", "README.md", "tools");
        RunScenarioGit(root, "commit", "-m", "fixture base");
        var candidatePath = scenario == "stale-values"
            ? Path.Combine(root, "Golden", "values-kernels.toml")
            : Path.Combine(root, "README.md");
        Directory.CreateDirectory(Path.GetDirectoryName(candidatePath)!);
        File.AppendAllText(candidatePath, "candidate\n");
        RunScenarioGit(root, "add", Path.GetRelativePath(root, candidatePath));
        RunScenarioGit(root, "commit", "-m", "fixture candidate");
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
            if [[ "${1:-}" == build && "$*" == *BannedApiCompileFailProof.csproj* ]]; then
              skipped=0
              while IFS=: read -r line _; do
                if [[ "${PREFLIGHT_SCENARIO:-}" == banned-api-diagnostic-mismatch && "$skipped" -eq 0 ]]; then
                  skipped=1
                  continue
                fi
                printf '%s(%s,1): error RS0030: fixture banned API\n' \
                  'tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs' "$line" >&2
              done < <(grep -nF '// banned-api-proof' \
                tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs)
              exit 1
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
            original="$*"
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
              semantic-test:tools:engineering-tests)
                [[ "$original" != *"MODE=execute"* ]] || exit 41
                ;;
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

        var result = TestProcessRunner.Run(
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
            BoundedProcessRunner.HangDetectionBudget,
            64 * 1024);

        return result;
    }

    private static void CopyPreflightScriptClosure(string sourceRoot, string destinationRoot)
    {
        var sourceScripts = Path.Combine(sourceRoot, "tools", "scripts");
        foreach (var source in Directory.GetFiles(
            sourceScripts,
            "*",
            SearchOption.AllDirectories))
        {
            var relativePath = Path.GetRelativePath(sourceRoot, source);
            var destination = Path.Combine(destinationRoot, relativePath);
            Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
            File.Copy(source, destination);
        }
    }

    private static void RunScenarioGit(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/git",
            arguments,
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                System.Text.Encoding.UTF8.GetString(result.StandardError));
        }
    }

    private static string RunScenarioGitForOutput(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/git",
            arguments,
            root,
            TestBudgets.ScriptProcessHangGuard,
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
