using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
    [Fact]
    public void ScribeContentChecksUseTheExplicitNonEmptyReport()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var explicitReport = Path.Combine(fixture.Path, "explicit-report.json");
        var ambientReport = Path.Combine(fixture.Path, "ambient-report.json");
        var scribe = Path.Combine(fixture.Path, "StrataLint.Scribe.dll");
        var log = Path.Combine(fixture.Path, "scribe.log");
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(explicitReport, "explicit\n");
        File.WriteAllText(ambientReport, "ambient\n");
        File.WriteAllText(scribe, "fixture\n");
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            "#!/usr/bin/env bash\nprintf '%s|%s\\n' \"$STRATALINT_LEAN_REPORT\" \"$*\" >> \"$SCRIBE_LOG\"");

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:/usr/bin:/bin\" STRATALINT_LEAN_REPORT=\"$2\" SCRIBE_LOG=\"$3\" "
                    + "exec /bin/bash \"$4\" \"$5\" \"$6\"",
                "scribe-content-checks",
                binDirectory,
                ambientReport,
                log,
                Path.Combine(root, ScribeContentChecksScriptPath),
                explicitReport,
                scribe,
            ],
            root,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        var invocations = File.ReadAllLines(log);
        Assert.Equal(4, invocations.Length);
        Assert.All(invocations, line => Assert.StartsWith(explicitReport + "|", line, StringComparison.Ordinal));
        Assert.DoesNotContain(invocations, line => line.Contains(ambientReport, StringComparison.Ordinal));
        Assert.Contains(
            invocations,
            line => line.EndsWith($" projections --check --report {explicitReport}", StringComparison.Ordinal));
    }

    [Fact]
    public void ScribeContentChecksRejectMissingAndEmptyReportsBeforeRunningScribe()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var emptyReport = Path.Combine(fixture.Path, "empty-report.json");
        var missingReport = Path.Combine(fixture.Path, "missing-report.json");
        var scribe = Path.Combine(fixture.Path, "StrataLint.Scribe.dll");
        Directory.CreateDirectory(binDirectory);
        File.WriteAllText(emptyReport, string.Empty);
        File.WriteAllText(scribe, "fixture\n");
        WriteExecutable(Path.Combine(binDirectory, "dotnet"), "#!/usr/bin/env bash\nexit 0");

        foreach (var report in new[] { emptyReport, missingReport })
        {
            var result = BoundedProcessRunner.Run(
                "/bin/bash",
                [
                    "-c",
                    "PATH=\"$1:/usr/bin:/bin\" exec /bin/bash \"$2\" \"$3\" \"$4\"",
                    "scribe-content-checks-invalid-report",
                    binDirectory,
                    Path.Combine(root, ScribeContentChecksScriptPath),
                    report,
                    scribe,
                ],
                root,
                TimeSpan.FromSeconds(30),
                64 * 1024);

            Assert.NotEqual(0, result.ExitCode);
        }
    }

    [Fact]
    public void HarnessGateUsesExternalJudgeWithoutRestoreOrBuild()
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var candidateRoot = Path.Combine(fixture.Path, "candidate");
        var binDirectory = Path.Combine(fixture.Path, "bin");
        var report = Path.Combine(fixture.Path, "candidate-lean-report.json");
        var judge = Path.Combine(fixture.Path, "judge", "StrataLint.dll");
        var log = Path.Combine(fixture.Path, "dotnet.log");
        Directory.CreateDirectory(candidateRoot);
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(Path.GetDirectoryName(judge)!);
        File.WriteAllText(report, "{}\n");
        File.WriteAllText(judge, string.Empty);
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            printf '%s\n' "$*" >> "$DOTNET_LOG"
            case "${2:-}" in
              check|filemap-conform) exit 0 ;;
            esac
            exit 91
            """);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PATH=\"$1:/usr/bin:/bin\" DOTNET_LOG=\"$2\" exec /bin/bash \"$3\" "
                + "--candidate \"$4\" --base base --candidate-lean-report \"$5\" --judge-dll \"$6\"",
                "external-judge",
                binDirectory,
                log,
                Path.Combine(root, ".github", "scripts", "harness-gate.sh"),
                candidateRoot,
                report,
                judge,
            ],
            candidateRoot,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        Assert.Equal(0, result.ExitCode);
        var invocations = File.ReadAllLines(log);
        Assert.Equal(2, invocations.Length);
        Assert.DoesNotContain(invocations, line => line.Contains(" selftest", StringComparison.Ordinal));
        Assert.Single(invocations, line => line.Contains(" check --protected-base base", StringComparison.Ordinal));
        Assert.Single(invocations, line => line.EndsWith(" filemap-conform", StringComparison.Ordinal));
        Assert.DoesNotContain(invocations, line =>
            line.StartsWith("restore ", StringComparison.Ordinal)
            || line.StartsWith("build ", StringComparison.Ordinal)
            || line.StartsWith("msbuild ", StringComparison.Ordinal));
    }

    [Theory]
    [InlineData(1, 1, "FAIL:SEMANTIC")]
    [InlineData(2, 2, "FAIL:INFRASTRUCTURE")]
    [InlineData(3, 0, "PASS:NONE")]
    public void PreflightConsumesHarnessGateOutcomeAcrossTheFullChain(
        int admissionExitCode,
        int expectedExitCode,
        string expectedDeclaration)
    {
        if (OperatingSystem.IsWindows()) return;

        var root = TestRepositoryLayout.FindRoot();
        using var fixture = new TemporaryDirectory();
        var candidateRoot = Path.Combine(fixture.Path, "candidate");
        var homeDirectory = Path.Combine(fixture.Path, "home");
        var binDirectory = Path.Combine(homeDirectory, ".dotnet");
        var candidateDll = Path.Combine(candidateRoot, "bin", "candidate.dll");
        Directory.CreateDirectory(Path.GetDirectoryName(candidateDll)!);
        Directory.CreateDirectory(binDirectory);
        Directory.CreateDirectory(Path.Combine(candidateRoot, "tools", "scripts"));
        File.WriteAllText(candidateDll, string.Empty);
        File.WriteAllText(
            Path.Combine(candidateRoot, "tools", "scripts", "perf-event-lib.sh"),
            "perf_make_spool_dir() { mktemp -d; }\n"
            + "perf_capture_event() { :; }\n"
            + "perf_flush_events() { :; }\n");
        WriteGateOutcomeReportPair(candidateRoot);

        WriteGateOutcomeGitShim(binDirectory, candidateRoot);
        WriteGateOutcomeDotnetShim(binDirectory);
        WriteExecutable(
            Path.Combine(binDirectory, "lake"),
            "#!/usr/bin/env bash\n[[ \"${1:-}\" == --version ]] || exit 64\nexit 0");
        WriteGateOutcomeMakeShim(binDirectory);

        var result = BoundedProcessRunner.Run(
            "/bin/bash",
            [
                "-c",
                "PREFLIGHT_ADMISSION_RC=\"$1\" PREFLIGHT_CANDIDATE_ROOT=\"$2\" "
                + "PREFLIGHT_GATE=\"$3\" PREFLIGHT_LOCAL_GATE=\"$4\" "
                + "HOME=\"$5\" BASE=base PATH=\"$6:/usr/bin:/bin\" "
                + "exec /bin/bash \"$7\"",
                "preflight-gate-outcome",
                admissionExitCode.ToString(System.Globalization.CultureInfo.InvariantCulture),
                candidateRoot,
                Path.Combine(root, ".github", "scripts", "harness-gate.sh"),
                Path.Combine(root, LocalHarnessGateScriptPath),
                homeDirectory,
                binDirectory,
                Path.Combine(root, PreflightScriptPath),
            ],
            candidateRoot,
            TimeSpan.FromSeconds(30),
            64 * 1024);

        var output = Encoding.UTF8.GetString(result.StandardOutput);
        var error = Encoding.UTF8.GetString(result.StandardError);
        Assert.True(
            expectedExitCode == result.ExitCode,
            $"expected exit {expectedExitCode}, actual {result.ExitCode}\nstdout:\n{output}\nstderr:\n{error}");
        Assert.EndsWith(
            $"FKST_LOCAL_ITERATION_RESULT:v2:{expectedDeclaration}\n",
            output,
            StringComparison.Ordinal);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteGateOutcomeGitShim(string binDirectory, string candidateRoot) =>
        WriteExecutable(
            Path.Combine(binDirectory, "git"),
            $$"""
            #!/usr/bin/env bash
            if [[ "${1:-}" == -C ]]; then shift 2; fi
            case "$*" in
              "rev-parse --show-toplevel") printf '%s\n' '{{candidateRoot}}' ;;
              "rev-parse --verify base^{commit}"|"rev-parse --verify 0000000000000000000000000000000000000001^{commit}") printf '%040d\n' 1 ;;
              "rev-parse --verify HEAD^{commit}"|"rev-parse --verify HEAD") printf '%040d\n' 2 ;;
              "merge-base --is-ancestor "*) exit 0 ;;
              *) echo "unexpected git invocation: $*" >&2; exit 90 ;;
            esac
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteGateOutcomeDotnetShim(string binDirectory) =>
        WriteExecutable(
            Path.Combine(binDirectory, "dotnet"),
            """
            #!/usr/bin/env bash
            case "${1:-}" in
              --version|restore) exit 0 ;;
              build)
                [[ "$*" != *CompileFailProof.csproj* ]] || exit 1
                exit 0
                ;;
              msbuild)
                project_root="${2%%/tools/*}"
                printf '%s/bin/candidate.dll\n' "$project_root"
                exit 0
                ;;
            esac
            if [[ "${2:-}" == selftest ]]; then printf 'selftest\n'; exit 0; fi
            if [[ "${2:-}" == check ]]; then exit "$PREFLIGHT_ADMISSION_RC"; fi
            if [[ "${2:-}" == filemap-conform ]]; then exit 0; fi
            if [[ "$*" == *StrataLint.Scribe.csproj* && "$*" == *" --check"* ]]; then exit 0; fi
            echo "unexpected dotnet invocation: $*" >&2
            exit 91
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteGateOutcomeMakeShim(string binDirectory) =>
        WriteExecutable(
            Path.Combine(binDirectory, "make"),
            """
            #!/usr/bin/env bash
            target=""
            gate_args=""
            for arg in "$@"; do
              case "$arg" in
                gate|dotnet|lean-report|test|selftest) target="$arg" ;;
                GATE_ARGS=*) gate_args="${arg#GATE_ARGS=}" ;;
              esac
            done
            if [[ "$target" == lean-report ]]; then
              report="$PREFLIGHT_CANDIDATE_ROOT/.lake/build/stratalint/raw-lean-report.json"
              mkdir -p "$(dirname "$report")"
              printf '{}\n' > "$report"
              exit 0
            fi
            [[ "$target" == gate ]] || exit 0
            [[ "$gate_args" == --skip-engineering ]] || exit 92
            "$PREFLIGHT_LOCAL_GATE" \
              --candidate "$PREFLIGHT_CANDIDATE_ROOT" \
              --base 0000000000000000000000000000000000000001 \
              --skip-engineering
            """);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void WriteGateOutcomeReportPair(string candidateRoot)
    {
        var gateDirectory = Path.Combine(candidateRoot, ".github", "scripts");
        Directory.CreateDirectory(gateDirectory);
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), ".github", "scripts", "harness-gate.sh"),
            Path.Combine(gateDirectory, "harness-gate.sh"));
        File.SetUnixFileMode(
            Path.Combine(gateDirectory, "harness-gate.sh"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var producerDirectory = Path.Combine(candidateRoot, "tools", "lean-inspector");
        Directory.CreateDirectory(producerDirectory);
        WriteExecutable(
            Path.Combine(producerDirectory, "inspect.sh"),
            "#!/usr/bin/env bash\nexit 0");
        File.WriteAllText(Path.Combine(producerDirectory, "Inspector.lean"), "fixture\n");
        var workflowDirectory = Path.Combine(candidateRoot, "tools", "scripts", "workflow");
        Directory.CreateDirectory(workflowDirectory);
        File.Copy(
            Path.Combine(TestRepositoryLayout.FindRoot(), ScribeContentChecksScriptPath),
            Path.Combine(workflowDirectory, "scribe-content-checks.sh"));
        var script = Path.Combine(candidateRoot, "tools", "scripts", "lean-report-pair.sh");
        WriteExecutable(
            script,
            """
            #!/usr/bin/env bash
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --candidate-output) candidate_output="$2"; shift 2 ;;
                --single) shift ;;
                *) shift 2 ;;
              esac
            done
            mkdir -p "$(dirname "$candidate_output")"
            printf '{}\n' > "$candidate_output"
            """);
    }
}
