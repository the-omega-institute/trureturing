using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DailyFullTestScriptTests
{
    private const string ScriptPath = "tools/scripts/workflow/daily-full-test.sh";

    [Fact]
    public void RunExecutesToolTestsBeforeContentWithoutLiveReportEnvironment()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();

        var result = fixture.Run(contentExit: 0, toolsExit: 17);

        Assert.Equal(1, result.ExitCode);
        var calls = fixture.Calls();
        Assert.Equal("-C tools test|CI=true|REQUIRE=|REPORT=", calls[0]);
        Assert.Equal("test|CI=true|REQUIRE=|REPORT=", calls[1]);
        Assert.Equal(
            ["content_exit=0", "tools_exit=17"],
            File.ReadAllLines(Path.Combine(fixture.LogsPath, "result.env")));
        Assert.Contains(
            "DAILY_FULL_TEST_RESULT content_exit=0 tools_exit=17",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void ReportCreatesAssignedIssueWithRunAndNamedFailures()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();
        fixture.WriteFailureLogs();

        var result = fixture.Report();

        Assert.Equal(0, result.ExitCode);
        var diagnostic = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("DAILY_GH_CALL issue create", diagnostic, StringComparison.Ordinal);
        Assert.Contains("--assignee loning", diagnostic, StringComparison.Ordinal);
        Assert.Contains("--repo the-omega-institute/trureturing", diagnostic, StringComparison.Ordinal);
        Assert.Contains("https://github.com/the-omega-institute/trureturing/actions/runs/12345", diagnostic, StringComparison.Ordinal);
        Assert.Contains("0123456789abcdef0123456789abcdef01234567", diagnostic, StringComparison.Ordinal);
        Assert.Contains("Example.Tests.ContractBreaks [FAIL]", diagnostic, StringComparison.Ordinal);
        Assert.Contains("D5/S0/Example.lean:12:4: error: declaration uses 'sorry'", diagnostic, StringComparison.Ordinal);
    }

    [Fact]
    public void ReportStillCreatesIssueWhenTheTestJobProducedNoLogs()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();

        var result = fixture.Report();

        Assert.Equal(0, result.ExitCode);
        var diagnostic = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("not produced", diagnostic, StringComparison.Ordinal);
        Assert.Contains(
            "[FAIL] workflow job Run both full test layers (test identity not produced)",
            diagnostic,
            StringComparison.Ordinal);
        Assert.Contains("DAILY_GH_CALL issue create", diagnostic, StringComparison.Ordinal);
    }

    [Fact]
    public void ReportUpdatesTheOpenOwnedIncidentWithoutOpeningDuplicate()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new Fixture();
        fixture.WriteFailureLogs();

        var result = fixture.Report(existingIssue: true);

        Assert.True(
            result.ExitCode == 0,
            Encoding.UTF8.GetString(result.StandardError));
        var calls = fixture.Calls();
        Assert.Contains(calls, call => call.StartsWith("issue list", StringComparison.Ordinal));
        Assert.Contains(calls, call => call.StartsWith("issue edit 321", StringComparison.Ordinal));
        Assert.Contains(calls, call => call.StartsWith("issue comment 321", StringComparison.Ordinal));
        Assert.DoesNotContain(calls, call => call.StartsWith("issue create", StringComparison.Ordinal));
        var diagnostic = Encoding.UTF8.GetString(result.StandardError);
        Assert.Contains("https://github.com/the-omega-institute/trureturing/actions/runs/12345", diagnostic, StringComparison.Ordinal);
        Assert.Contains("Example.Tests.ContractBreaks [FAIL]", diagnostic, StringComparison.Ordinal);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class Fixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();
        private readonly string repository;
        private readonly string script;
        private readonly string bin;
        private readonly string calls;

        internal Fixture()
        {
            repository = Path.Combine(temporary.Path, "repository");
            script = Path.Combine(repository, ScriptPath);
            bin = Path.Combine(temporary.Path, "bin");
            calls = Path.Combine(temporary.Path, "calls");
            LogsPath = Path.Combine(temporary.Path, "logs");
            ScriptHarnessScratch.EnsureDirectory(bin);
            ScriptHarnessScratch.EnsureDirectory(LogsPath);
            ScriptHarnessScratch.CopyScriptInto(
                Path.Combine(TestRepositoryLayout.FindRoot(), ScriptPath),
                script);
            ScriptHarnessScratch.WriteExecutableStub(
                Path.Combine(bin, "make"),
                "printf '%s|CI=%s|REQUIRE=%s|REPORT=%s\\n' \"$*\" \"${CI:-}\" \"${STRATALINT_REQUIRE_LIVE_REPORT:-}\" \"${STRATALINT_LEAN_REPORT:-}\" >> \"$DAILY_TEST_CALLS\"\n"
                + "case \"$*\" in\n"
                + "  test) printf '%s\\n' 'content target output'; exit \"$DAILY_CONTENT_EXIT\";;\n"
                + "  '-C tools test') printf '%s\\n' 'tools target output'; exit \"$DAILY_TOOLS_EXIT\";;\n"
                + "  *) exit 99;;\n"
                + "esac");
            ScriptHarnessScratch.WriteExecutableStub(
                Path.Combine(bin, "gh"),
                "printf '%s\\n' \"$*\" >> \"$DAILY_GH_CALLS\"\n"
                + "printf 'DAILY_GH_CALL %s\\n' \"$*\" >&2\n"
                + "if [[ $1 == issue && $2 == list ]]; then\n"
                + "  if [[ -n ${DAILY_EXISTING_ISSUE:-} ]]; then\n"
                + "    printf '321\\t%s\\t%s\\n' \"$DAILY_EXPECTED_TITLE\" \"$DAILY_EXISTING_ISSUE\"\n"
                + "  fi\n"
                + "  exit 0\n"
                + "fi\n"
                + "if [[ $1 == issue && $2 == edit ]]; then exit 0; fi\n"
                + "body_file=''\n"
                + "while [[ $# -gt 0 ]]; do\n"
                + "  if [[ $1 == --body-file ]]; then body_file=$2; shift 2; else shift; fi\n"
                + "done\n"
                + "cat \"$body_file\" >&2\n"
                + "printf '%s\\n' 'https://github.com/the-omega-institute/trureturing/issues/999'");
        }

        internal string LogsPath { get; }

        internal ProcessOutput Run(int contentExit, int toolsExit) =>
            Execute(
                [
                    $"DAILY_TEST_CALLS={calls}",
                    $"DAILY_CONTENT_EXIT={contentExit}",
                    $"DAILY_TOOLS_EXIT={toolsExit}",
                    "STRATALINT_REQUIRE_LIVE_REPORT=1",
                    "STRATALINT_LEAN_REPORT=/poisoned/report.json",
                ],
                "run",
                LogsPath);

        internal ProcessOutput Report(bool existingIssue = false) =>
            Execute(
                [
                    $"DAILY_GH_CALLS={calls}",
                    "GH_TOKEN=test-token",
                    "GITHUB_REPOSITORY=the-omega-institute/trureturing",
                    "GITHUB_SERVER_URL=https://github.com",
                    "GITHUB_RUN_ID=12345",
                    "GITHUB_RUN_ATTEMPT=2",
                    "GITHUB_SHA=0123456789abcdef0123456789abcdef01234567",
                    "GITHUB_EVENT_NAME=schedule",
                    "DAILY_FAILURE_ASSIGNEE=loning",
                    "DAILY_EXPECTED_TITLE=Daily full-test backstop is failing",
                    $"DAILY_EXISTING_ISSUE={(existingIssue ? "https://github.com/the-omega-institute/trureturing/issues/999" : string.Empty)}",
                ],
                "report",
                LogsPath);

        internal void WriteFailureLogs()
        {
            File.WriteAllText(
                Path.Combine(LogsPath, "result.env"),
                "content_exit=1\ntools_exit=1\n");
            File.WriteAllText(
                Path.Combine(LogsPath, "content.log"),
                "D5/S0/Example.lean:12:4: error: declaration uses 'sorry'\n");
            File.WriteAllText(
                Path.Combine(LogsPath, "tools.log"),
                "[xUnit.net 00:00:01.00]     Example.Tests.ContractBreaks [FAIL]\n");
        }

        internal string[] Calls() => ScriptHarnessScratch.ReadScratchLines(calls);

        private ProcessOutput Execute(
            IReadOnlyList<string> environment,
            params string[] arguments) =>
            TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={bin}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    .. environment,
                    "/bin/bash",
                    script,
                    .. arguments,
                ],
                repository,
                TestBudgets.ScriptProcessHangGuard,
                128 * 1024);

        public void Dispose() => temporary.Dispose();
    }
}
