using System.Text;
using StrataLint.TestSupport;

namespace StrataLint.Lean.Tests;

public sealed class LeanReportSelectionTests
{
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
