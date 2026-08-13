using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class MakeWorkflowTests
{
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

        var root = FindRepositoryRoot();
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
            Path.Combine(FindRepositoryRoot(), ".github", "scripts", "harness-gate.sh"),
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
