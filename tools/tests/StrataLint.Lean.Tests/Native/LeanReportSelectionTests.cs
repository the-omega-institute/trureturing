using System.Text;
using System.Text.Json;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanReportSelectionTests
{
    [Theory]
    [InlineData("probe", "none", false)]
    [InlineData("reuse", "none", false)]
    [InlineData("probe", "source", true)]
    [InlineData("probe", "toolchain", true)]
    [InlineData("probe", "environment", true)]
    [InlineData("reuse", "material", true)]
    [InlineData("probe", "old-receipt", true)]
    public void ReportReuseChecksDeclaredInputsWithoutInstalledToolchain(string operation, string change, bool needsLake)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import json, os, pathlib, sys
            root, operation, change = sys.argv[1:]
            sys.path.insert(0, str(pathlib.Path(root) / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            fixture = ReuseTests()
            fixture.setUp()
            try:
                api = fixture.receipt()
                fixture.lake.unlink()
                fixture.lake.with_name('lean').unlink()
                if change == 'source': fixture.write('D5/A.lean', 'def changed := 2\n')
                if change == 'toolchain': fixture.write('lean-toolchain', 'changed-toolchain\n')
                if change == 'environment': os.environ['LEAN_OPTS'] = '-DmaxRecDepth=100'
                if change == 'material': pathlib.Path(str(fixture.report) + '.materials.zip').write_bytes(b'corrupt')
                if change == 'old-receipt':
                    receipt = pathlib.Path(str(fixture.report) + '.reuse.json')
                    record = json.loads(receipt.read_text())
                    record['schema'] = 'stratalint-lean-report-reuse-v1'
                    receipt.write_text(json.dumps(record))
                if operation == 'probe': outcome = api.probe(fixture.root, fixture.report)
                else: outcome = api.reuse(fixture.root, fixture.report, fixture.output)
                outcome['published'] = fixture.output.exists()
                print(json.dumps(outcome))
            finally:
                fixture.doCleanups()
            """, root, operation, change], root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.True(result.ExitCode == 0, text + Encoding.UTF8.GetString(result.StandardError));
        using var outcome = JsonDocument.Parse(text);
        Assert.Equal(needsLake, outcome.RootElement.GetProperty("needs_lake").GetBoolean());
        Assert.Equal(operation == "reuse" && !needsLake, outcome.RootElement.GetProperty("published").GetBoolean());
    }

    [Theory]
    [InlineData("missing")]
    [InlineData("different-path")]
    [InlineData("unregistered")]
    [InlineData("excluded")]
    public void ExecutionToolchainMustBeAnExplicitRequiredInput(string defect)
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import pathlib, sys
            sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            import publication
            fixture = ReuseTests()
            fixture.setUp()
            try:
                defect = sys.argv[2]
                if defect == 'missing': del fixture.policy['report_execution']['toolchain']
                if defect == 'different-path': fixture.policy['report_execution']['toolchain'] = 'unregistered/pin'
                if defect == 'unregistered': fixture.policy['config_inputs']['include'] = []
                if defect == 'excluded': fixture.policy['config_inputs']['exclude'] = ['lean-toolchain']
                fixture.write_policy()
                try: publication.selection.Selection(fixture.root).validate('lean-report')
                except ValueError as error:
                    print(error)
                    raise SystemExit(4)
            finally:
                fixture.doCleanups()
            """, root, defect], root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        Assert.Equal(4, result.ExitCode);
        Assert.Contains("lean-report-inputs.json", Encoding.UTF8.GetString(result.StandardOutput), StringComparison.Ordinal);
    }

    [Fact]
    public void ReportEntryReusesValidatedReportWithoutInstalledToolchain()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import pathlib, sys
            sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            fixture = ReuseTests()
            fixture.setUp()
            original = fixture.receipt
            def prepare():
                api = original()
                fixture.lake.unlink()
                fixture.lake.with_name('lean').unlink()
                return api
            fixture.receipt = prepare
            try:
                result, calls = fixture.entry_with_program_build([])
                print(result.stdout, end='')
                print(result.stderr, end='', file=sys.stderr)
                if calls: print('UNEXPECTED_BUILD ' + repr(calls))
                raise SystemExit(result.returncode)
            finally:
                fixture.doCleanups()
            """, root], root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.True(result.ExitCode == 0, text + Encoding.UTF8.GetString(result.StandardError));
        Assert.Contains("LEAN_INSPECTOR_WORK extracted_modules=0 aggregates=0", text, StringComparison.Ordinal);
        Assert.DoesNotContain("UNEXPECTED_BUILD", text, StringComparison.Ordinal);
    }

    [Fact]
    public void DamagedReportAfterResourceProbeStillObtainsToolchainAndRunsNormalBuild()
    {
        if (OperatingSystem.IsWindows()) return;
        var root = TestRepositoryLayout.FindRoot();
        var result = TestProcessRunner.Run("python3", ["-B", "-c", """
            import json, os, pathlib, shutil, subprocess, sys, zipfile
            sys.path.insert(0, str(pathlib.Path(sys.argv[1]) / 'tools/lean-inspector/tests'))
            from test_reuse import ReuseTests
            import publication, reuse
            fixture = ReuseTests()
            fixture.setUp()
            try:
                first, calls = fixture.entry_with_program_build([], build_exit=37)
                if first.returncode: raise RuntimeError(first.stdout + first.stderr)
                probe = reuse.probe(fixture.root, fixture.report)
                archive = publication.member(fixture.report, '.materials.zip')
                with zipfile.ZipFile(archive, 'w') as output: output.writestr('unreferenced', b'bad material')
                receipt = publication.member(fixture.report, '.reuse.json')
                record = json.loads(receipt.read_text())
                record['bundle']['.materials.zip'] = publication.digest(archive)
                receipt.write_text(json.dumps(record))
                shutil.rmtree(fixture.root / '.lake')
                installed = fixture.root / 'installed'
                installed.mkdir()
                fixture.lake.rename(installed / 'lake')
                fixture.lake.with_name('lean').unlink()
                executables = fixture.root / 'exec'
                executables.mkdir()
                (executables / 'python3').symlink_to(sys.executable)
                fixture.write('tools/scripts/workflow/install-lean-toolchain.sh',
                    '#!/bin/bash\nset -euo pipefail\nprintf "toolchain\\n" >> build-calls\n'
                    + 'test "$1" -ef "' + str(fixture.root / 'lean-toolchain') + '"\n'
                    + 'test "$2" = --github-path\nprintf "%s\\n" "' + str(installed) + '" > "$3"\n')
                installer = fixture.root / 'tools/scripts/workflow/install-lean-toolchain.sh'
                installer.chmod(0o755)
                environment = dict(os.environ, PATH=str(executables) + ':/usr/bin:/bin',
                    STRATALINT_INSPECTOR_SUPERVISED='1', STRATALINT_LEAN_BUILD_TARGETS='[]',
                    STRATALINT_LEAN_REPORT_REUSE=str(fixture.report),
                    STRATALINT_LEAN_PRODUCER_DLL=str(fixture.root / 'producer.dll'))
                environment.pop('LAKE_BIN', None)
                second = subprocess.run(['/bin/bash', str(fixture.root / 'tools/lean-inspector/inspect.sh'),
                    '--repository', str(fixture.root), '--output', str(fixture.output)],
                    env=environment, text=True, capture_output=True, cwd=fixture.root)
                path = fixture.root / 'build-calls'
                print(json.dumps(dict(probe=probe, exit=second.returncode, stdout=second.stdout,
                    stderr=second.stderr, calls=path.read_text().splitlines() if path.exists() else [])))
            finally:
                fixture.doCleanups()
            """, root], root, TestBudgets.WorkflowProcessHangGuard, 1024 * 1024);
        var text = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.True(result.ExitCode == 0, text + Encoding.UTF8.GetString(result.StandardError));
        using var outcome = JsonDocument.Parse(text);
        Assert.False(outcome.RootElement.GetProperty("probe").GetProperty("needs_lake").GetBoolean());
        Assert.True(outcome.RootElement.GetProperty("exit").GetInt32() == 37, text);
        var calls = outcome.RootElement.GetProperty("calls").EnumerateArray().Select(item => item.GetString()).ToArray();
        Assert.Equal(3, calls.Length);
        Assert.Equal("toolchain", calls[0]);
        Assert.Equal("ensure", calls[1]);
        Assert.EndsWith(" build :report", calls[2]);
    }

    public static IEnumerable<object[]> InspectorPhaseCases()
    {
        foreach (var buildProducer in new[] { false, true })
        foreach (var unavailableClock in new[] { false, true })
        foreach (var failedPhase in buildProducer
                     ? new[] { "", "inputs", "reuse", "capture", "utility-input-build", "ensure", "report", "publish", "seal" }
                     : new[] { "", "inputs", "reuse", "capture", "ensure", "report", "publish", "seal" })
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
            [[ "${1:-}" != -B ]] || shift
            case "$1" in
              */lean-report-selection.py) phase=inputs ;;
              */native.py) phase=publish ;;
              */reuse.py) phase="$2" ;;
              *) exit 97 ;;
            esac
            printf '%s\n' "$phase" >> "$INSPECTOR_TEST_PHASES"
            [[ "$phase" != "$INSPECTOR_TEST_FAILURE" ]] || exit 23
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
            "STRATALINT_INSPECTOR_SUPERVISED=1", "STRATALINT_LEAN_BUILD_TARGETS=[]", "LAKE_BIN=" + lake,
            "INSPECTOR_TEST_PHASES=" + phases, "INSPECTOR_TEST_FAILURE=" + failedPhase,
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
            ? new[] { "inputs", "reuse", "capture", "utility-input-build", "ensure", "report", "publish", "seal" }
            : new[] { "inputs", "reuse", "capture", "ensure", "report", "publish", "seal" };
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
