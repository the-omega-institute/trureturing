using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanReportSelectionTests
{
    public static IEnumerable<object[]> InspectorPhaseCases()
    {
        foreach (var buildProducer in new[] { false, true })
        foreach (var unavailableClock in new[] { false, true })
        foreach (var failedPhase in buildProducer
                     ? new[] { "", "inputs", "compiler", "reuse", "capture", "utility-input-build", "ensure", "report", "publish", "seal" }
                     : new[] { "", "inputs", "compiler", "reuse", "capture", "ensure", "report", "publish", "seal" })
            yield return [failedPhase, unavailableClock, buildProducer];
    }

    [Theory]
    [MemberData(nameof(InspectorPhaseCases))]
    public void InspectorPhaseTimingPreservesProductionAndFailure(
        string failedPhase, bool unavailableClock, bool buildProducer)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var fixture = Path.Combine(temporary.Path, "candidate repository");
        var inspector = Path.Combine(fixture, "tools/lean-inspector/inspect.sh");
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/lean-inspector/inspect.sh"), inspector);
        ScriptHarnessScratch.EnsureDirectory(Path.Combine(fixture, "tools/scripts/lib"));
        ScriptHarnessScratch.EnsureDirectory(Path.Combine(fixture, "tools/scripts/worktree"));
        ScriptHarnessScratch.WriteScratchText(Path.Combine(fixture, "tools/scripts/lib/resource-observation-lib.sh"),
            "resource_observe() { :; }\n");
        var stubDirectory = Path.Combine(fixture, "fixture-bin");
        ScriptHarnessScratch.EnsureDirectory(stubDirectory);
        ScriptHarnessScratch.WriteExecutableStub(Path.Combine(stubDirectory, "python3"), """
            if [[ "${1:-}" == -I ]]; then
              printf '%s/bin/lake\n' "$INSPECTOR_TEST_COMPILER"
              exit 0
            fi
            [[ "${1:-}" != -B ]] || shift
            case "$1" in
              */lean-report-selection.py) phase=inputs ;;
              */compiler/build.py) phase=compiler ;;
              */native.py) phase=publish ;;
              */reuse.py) phase="$2" ;;
              *) exit 97 ;;
            esac
            printf '%s\n' "$phase" >> "$INSPECTOR_TEST_PHASES"
            [[ "$phase" != "$INSPECTOR_TEST_FAILURE" ]] || exit 23
            [[ "$phase" != compiler ]] || printf '{"directory":"%s"}\n' "$INSPECTOR_TEST_COMPILER"
            [[ "$phase" != reuse ]] || exit 3
            if [[ "$phase" == capture ]]; then
              while [[ $# -gt 0 ]]; do
                if [[ "$1" == --snapshot ]]; then printf '{}\n' > "$2"; break; fi
                shift
              done
            fi
            if [[ "$phase" == publish ]]; then
              printf 'published\n' > "$4"
              printf 'fixture report published\n'
            fi
            """);
        ScriptHarnessScratch.WriteExecutableStub(Path.Combine(stubDirectory, "dotnet"), """
            printf 'utility-input-build\n' >> "$INSPECTOR_TEST_PHASES"
            [[ "$INSPECTOR_TEST_FAILURE" != utility-input-build ]] || exit 23
            """);
        ScriptHarnessScratch.WriteExecutableStub(Path.Combine(fixture, "tools/scripts/worktree/lean-cache-ensure.sh"), """
            printf 'ensure\n' >> "$INSPECTOR_TEST_PHASES"
            [[ "$INSPECTOR_TEST_FAILURE" != ensure ]] || exit 23
            """);
        ScriptHarnessScratch.WriteExecutableStub(Path.Combine(fixture, "tools/scripts/worktree/lean-cache-run.sh"), """
            printf 'report\n' >> "$INSPECTOR_TEST_PHASES"
            [[ "$INSPECTOR_TEST_FAILURE" != report ]] || exit 23
            "$@"
            """);
        var lake = Path.Combine(stubDirectory, "lake");
        ScriptHarnessScratch.WriteExecutableStub(lake, "exit 0\n");
        var compiler = Path.Combine(fixture, "verified compiler");
        ScriptHarnessScratch.EnsureDirectory(Path.Combine(compiler, "bin"));
        ScriptHarnessScratch.WriteExecutableStub(Path.Combine(compiler, "bin/lake"), "exit 0\n");
        var producer = Path.Combine(fixture, "fixture-producer.dll");
        ScriptHarnessScratch.WriteScratchText(producer, "fixture producer");
        var shellEnvironment = Path.Combine(fixture, "fixture-shell-env");
        ScriptHarnessScratch.WriteScratchText(shellEnvironment, unavailableClock ? "unset SECONDS\n" : "# default shell clock\n");
        var phases = Path.Combine(temporary.Path, "phases");
        var report = Path.Combine(fixture, "published.json");
        var logs = Path.Combine(fixture, "diagnostics");
        var arguments = new List<string>
        {
            "-u", "STRATALINT_LEAN_PRODUCER_DLL",
            "STRATALINT_INSPECTOR_SUPERVISED=1", "LAKE_BIN=" + lake,
            "INSPECTOR_TEST_PHASES=" + phases, "INSPECTOR_TEST_FAILURE=" + failedPhase,
            "INSPECTOR_TEST_COMPILER=" + compiler,
            "BASH_ENV=" + shellEnvironment,
            "PATH=" + stubDirectory + Path.PathSeparator + Environment.GetEnvironmentVariable("PATH"),
        };
        if (!buildProducer) arguments.Add("STRATALINT_LEAN_PRODUCER_DLL=" + producer);
        arguments.AddRange(["bash", inspector, "--repository", fixture, "--output", report, "--log-dir", logs]);
        var result = TestProcessRunner.Run("env", arguments,
            temporary.Path, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);

        Assert.True(result.ExitCode == (failedPhase.Length == 0 ? 0 : 23),
            $"[FAIL] inspector_phase_exit_{failedPhase}: actual={result.ExitCode}");
        var allPhases = buildProducer
            ? new[] { "inputs", "compiler", "reuse", "capture", "utility-input-build", "ensure", "report", "publish", "seal" }
            : new[] { "inputs", "compiler", "reuse", "capture", "ensure", "report", "publish", "seal" };
        var expected = failedPhase.Length == 0 ? allPhases : allPhases.Take(Array.IndexOf(allPhases, failedPhase) + 1).ToArray();
        Assert.Equal(expected, ScriptHarnessScratch.ReadRecordedCalls(phases));
        Assert.Equal(failedPhase.Length == 0 || failedPhase == "seal", File.Exists(report));
        var standardOutput = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Equal(failedPhase.Length == 0 ? "fixture report published\n" : "", standardOutput);
        Assert.DoesNotContain("LEAN_INSPECTOR_PHASE", standardOutput, StringComparison.Ordinal);
        Assert.DoesNotContain("LEAN_INSPECTOR_FAILED", standardOutput, StringComparison.Ordinal);
        var error = Encoding.UTF8.GetString(result.StandardError);
        var observations = error.Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Where(line => line.StartsWith("LEAN_INSPECTOR_PHASE ", StringComparison.Ordinal)).ToArray();
        Assert.Equal(expected.Length * 2, observations.Length);
        for (var index = 0; index < expected.Length; index++)
        {
            var phase = expected[index];
            Assert.StartsWith($"LEAN_INSPECTOR_PHASE phase={phase} status=started clock=shell-seconds start_seconds=", observations[2 * index]);
            var completed = observations[2 * index + 1];
            Assert.StartsWith($"LEAN_INSPECTOR_PHASE phase={phase} status=completed clock=shell-seconds ", completed);
            Assert.EndsWith("exit=" + (phase == failedPhase ? 23 : 0), completed);
            Assert.Matches(unavailableClock
                ? "start_seconds=unavailable end_seconds=unavailable elapsed_seconds=unavailable exit="
                : "start_seconds=[0-9]+ end_seconds=[0-9]+ elapsed_seconds=[0-9]+ exit=", completed);
        }
        if (failedPhase.Length != 0)
            Assert.Contains($"LEAN_INSPECTOR_FAILED phase={failedPhase} exit=23", error, StringComparison.Ordinal);
        if (File.Exists(Path.Combine(logs, "native-work.jsonl")))
            Assert.Empty(ScriptHarnessScratch.ReadScratchText(Path.Combine(logs, "native-work.jsonl")));
    }

    [Theory]
    [InlineData("registration_failures")]
    [InlineData("glob_semantics")]
    [InlineData("source_and_policy_identity")]
    [InlineData("source_traversal_io")]
    public void RegisteredSelectionContract(string scenario)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3",
            ["-B", Path.Combine(root, "tools/tests/StrataLint.Lean.Tests/Native/lean_report_selection_fixture.py"),
                root, temporary.Path, scenario], temporary.Path,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.True(result.ExitCode == 0, Encoding.UTF8.GetString(result.StandardOutput)
            + Encoding.UTF8.GetString(result.StandardError));
    }

    [Theory]
    [InlineData("absolute", 0)]
    [InlineData("relative", 0)]
    [InlineData("absolute", 23)]
    [InlineData(null, 0)]
    [InlineData("", 0)]
    [InlineData(null, 23)]
    public void WrapperPassesLogDirectoryAndNativeExit(string? directoryMode, int nativeExit)
    {
        if (OperatingSystem.IsWindows()) return;
        using var temporary = new TemporaryDirectory();
        var fixture = Path.Combine(temporary.Path, "candidate repository");
        var wrapper = Path.Combine(fixture, "tools/scripts/report/lean-report.sh");
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/report/lean-report.sh"), wrapper);
        ScriptHarnessScratch.WriteScratchText(Path.Combine(fixture, "fixture.identity"), fixture);
        var inspector = Path.Combine(fixture, "tools/lean-inspector/inspect.sh");
        ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(inspector)!);
        ScriptHarnessScratch.WriteExecutableStub(inspector, """
            printf '%s\n' "$@" > "$LEAN_REPORT_TEST_ARGUMENTS"
            repository='' output='' log_dir=''
            while [[ $# -gt 0 ]]; do
              case "$1" in
                --repository) repository="$2" ;;
                --output) output="$2" ;;
                --log-dir) log_dir="$2" ;;
                *) exit 97 ;;
              esac
              shift 2
            done
            [[ "$output" == /* ]] || output="$repository/$output"
            [[ -n "$log_dir" ]] || log_dir="${output}.logs"
            [[ "$log_dir" == /* ]] || log_dir="$repository/$log_dir"
            mkdir -p "$log_dir"
            printf 'native phase output\n' > "$log_dir/report.stdout.log"
            printf '%s\n' "$LEAN_REPORT_TEST_EXIT" > "$log_dir/report.exit.log"
            exit "$LEAN_REPORT_TEST_EXIT"
            """);

        const string output = "reports/raw report.json";
        var argumentLog = Path.Combine(temporary.Path, "native arguments");
        var logDirectory = directoryMode switch
        {
            "absolute" => Path.Combine(fixture, "explicit diagnostic logs"),
            "relative" => "build/ci/current diagnostic logs",
            _ => directoryMode,
        };
        var arguments = new List<string>
        {
            "-u", "STRATALINT_LEAN_REPORT_LOG_DIR", "LEAN_REPORT=" + output,
            "LEAN_REPORT_TEST_ARGUMENTS=" + argumentLog,
            "LEAN_REPORT_TEST_EXIT=" + nativeExit,
        };
        if (logDirectory is not null)
            arguments.Add("STRATALINT_LEAN_REPORT_LOG_DIR=" + logDirectory);
        arguments.AddRange(["bash", wrapper]);
        var result = TestProcessRunner.Run("env", arguments, temporary.Path,
            TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);

        Assert.Equal(nativeExit, result.ExitCode);
        var recorded = ScriptHarnessScratch.ReadRecordedCalls(argumentLog);
        Assert.True(recorded.Length >= 4, Encoding.UTF8.GetString(result.StandardError));
        Assert.Equal(fixture, ScriptHarnessScratch.ReadScratchText(Path.Combine(recorded[1], "fixture.identity")));
        var expected = new List<string> { "--repository", recorded[1], "--output", output };
        if (!string.IsNullOrEmpty(logDirectory)) expected.AddRange(["--log-dir", logDirectory]);
        Assert.Equal(expected, recorded);
        var expectedLogDirectory = string.IsNullOrEmpty(logDirectory) ? output + ".logs" : logDirectory;
        if (!Path.IsPathRooted(expectedLogDirectory))
            expectedLogDirectory = Path.Combine(fixture, expectedLogDirectory);
        Assert.Equal("native phase output\n", ScriptHarnessScratch.ReadScratchText(
            Path.Combine(expectedLogDirectory, "report.stdout.log")));
        Assert.Equal(nativeExit + "\n", ScriptHarnessScratch.ReadScratchText(
            Path.Combine(expectedLogDirectory, "report.exit.log")));
    }
}
