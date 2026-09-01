using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe.Tests;

namespace StrataLint.Tests;

internal static class EngineeringTestReportScriptTests
{
    internal static void Verify()
    {
        ExecuteCapturesActualOutputAndPreservesTheExecuteExitCode();
        SuccessfulExecuteRecordsAnEmptyFailureTail();
        SummaryRetainsTheArtifactOutcomeAndDynamicTailFieldCommand();
    }

    private static void ExecuteCapturesActualOutputAndPreservesTheExecuteExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReportFixture(executeExit: 23);

        var result = fixture.Run("execute");

        Assert.Equal(23, result.ExitCode);
        Assert.EndsWith(
            ReportFixture.ExecutionOutput,
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
        Assert.False(TemporaryFileSystem.Directory.Exists(fixture.BaseHarnessRoot));

        var executionLog = TemporaryFileSystem.File.ReadAllText(fixture.ExecutionLogPath);
        Assert.Equal(ReportFixture.ExecutionOutput, executionLog);
        using var document = JsonDocument.Parse(
            TemporaryFileSystem.File.ReadAllText(fixture.ExecutionRecordPath));
        var record = document.RootElement;
        Assert.Equal(23, record.GetProperty("execute_exit").GetInt32());
        Assert.Equal("accepted", record.GetProperty("plan_verdict").GetString());
        Assert.Equal(
            "ENGINEERING_TEST_EVIDENCE_FAILED missing=1",
            Assert.Single(record.GetProperty("diagnostics").EnumerateArray()).GetString());
        Assert.Equal(
            executionLog.TrimEnd().Split('\n'),
            record.GetProperty("failure_tail").EnumerateArray().Select(item => item.GetString()));
    }

    private static void SuccessfulExecuteRecordsAnEmptyFailureTail()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReportFixture(executeExit: 0);

        var result = fixture.Run("execute");

        Assert.Equal(0, result.ExitCode);
        using var document = JsonDocument.Parse(
            TemporaryFileSystem.File.ReadAllText(fixture.ExecutionRecordPath));
        Assert.Empty(document.RootElement.GetProperty("failure_tail").EnumerateArray());
    }

    private static void SummaryRetainsTheArtifactOutcomeAndDynamicTailFieldCommand()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new ReportFixture(executeExit: 0);

        var result = fixture.Run("summarize");

        Assert.Equal(0, result.ExitCode);
        Assert.Equal(
            """
            ## Candidate engineering scope

            - Event: push
            - Test plan: selected
            - Dev parent: 9727fad6a0fde3f6324b113197dd7a42c64eb3c9
            - Changed paths: 2
            - Selected tests: 1
            - Planner fallback count: 0
            - Plan artifact upload: success
            - Detail: `gh run download 4399 --repo example/trureturing --name engineering-test-plan --dir engineering-test-plan-4399 && jq '{execute_exit, plan_verdict, diagnostics, plan, failure_tail}' engineering-test-plan-4399/engineering-test-plan.json`.

            """,
            TemporaryFileSystem.File.ReadAllText(fixture.SummaryPath));
    }

    private sealed class ReportFixture : IDisposable
    {
        internal const string ExecutionOutput =
            "ENGINEERING_TEST_PLAN state=selected\n"
            + "ENGINEERING_TEST_SELECTED StrataLint.Tests.Example\n"
            + "ENGINEERING_TEST_EVIDENCE_FAILED missing=1\n";

        private const string Head = "23747a66fdb518fd82dbccc6ca5fca0126d6d33c";
        private const string Base = "9727fad6a0fde3f6324b113197dd7a42c64eb3c9";
        private readonly TemporaryDirectory temporary = new();
        private readonly string binPath;
        private readonly string callsPath;
        private readonly string runnerTemp;
        private readonly string workspace;
        private readonly string scriptPath;
        private readonly int executeExit;

        internal ReportFixture(int executeExit)
        {
            this.executeExit = executeExit;
            binPath = Path.Combine(temporary.Path, "bin");
            callsPath = Path.Combine(temporary.Path, "calls");
            runnerTemp = Path.Combine(temporary.Path, "runner");
            workspace = Path.Combine(temporary.Path, "workspace");
            scriptPath = Path.Combine(temporary.Path, "engineering-test-report.sh");
            ScriptHarnessScratch.EnsureDirectory(binPath);
            ScriptHarnessScratch.EnsureDirectory(runnerTemp);
            ScriptHarnessScratch.EnsureDirectory(Path.Combine(workspace, "candidate"));
            RepositoryAccessor
                .Discover(RepositoryRootCriterion.ClaudeDirectoryNotFound)
                .CopyTo(
                    StrataLint.Scribe.Tests.RepositoryRelativePath.Create(
                        "tools/scripts/workflow/engineering-test-report.sh"),
                    scriptPath);
            WriteExecutable(
                "git",
                "printf 'git:%s\\n' \"$*\" >> \"$REPORT_CALLS\"\n"
                + "case \"$*\" in\n"
                + "  *'worktree add --detach'*) mkdir -p \"$REPORT_BASE_HARNESS_ROOT\";;\n"
                + "  *'rev-parse HEAD'*) printf '%s\\n' \"$ENGINEERING_BASE\";;\n"
                + "  *'worktree remove --force'*) rm -rf -- \"$REPORT_BASE_HARNESS_ROOT\";;\n"
                + "esac");
            WriteExecutable("dotnet", "printf 'dotnet:%s\\n' \"$*\" >> \"$REPORT_CALLS\"");
            WriteExecutable(
                "make",
                "printf 'make:%s\\n' \"$*\" >> \"$REPORT_CALLS\"\n"
                + "for argument in \"$@\"; do\n"
                + "  if [[ \"$argument\" == MODE=execute ]]; then\n"
                + "    printf '%s' \"$REPORT_EXECUTION_OUTPUT\"\n"
                + "    exit \"$REPORT_EXECUTE_EXIT\"\n"
                + "  fi\n"
                + "done");
        }

        internal string BaseHarnessRoot =>
            Path.Combine(runnerTemp, "protected-base-engineering-execution-harness");

        internal string ExecutionLogPath =>
            Path.Combine(runnerTemp, "engineering-test-plan-artifact", "engineering-test-execution.log");

        internal string ExecutionRecordPath =>
            Path.Combine(runnerTemp, "engineering-test-plan-artifact", "engineering-test-plan.json");

        internal string SummaryPath => Path.Combine(temporary.Path, "summary.md");

        internal ProcessOutput Run(string action) =>
            TestProcessRunner.Run(
                "/usr/bin/env",
                [
                    $"PATH={binPath}{Path.PathSeparator}{Environment.GetEnvironmentVariable("PATH")}",
                    $"REPORT_CALLS={callsPath}",
                    $"REPORT_BASE_HARNESS_ROOT={BaseHarnessRoot}",
                    $"REPORT_EXECUTE_EXIT={executeExit}",
                    $"REPORT_EXECUTION_OUTPUT={ExecutionOutput}",
                    $"RUNNER_TEMP={runnerTemp}",
                    $"GITHUB_WORKSPACE={workspace}",
                    "GITHUB_REPOSITORY=example/trureturing",
                    "GITHUB_RUN_ID=4399",
                    $"GITHUB_STEP_SUMMARY={SummaryPath}",
                    $"ENGINEERING_HEAD={Head}",
                    $"ENGINEERING_BASE={Base}",
                    "ENGINEERING_EXECUTION_FULL_REQUIRED=false",
                    "ENGINEERING_REPORT_SCHEMA={\"kind\":\"failure-report\",\"state\":\"resolved\",\"resolution\":{\"evidence_diagnostic_prefix\":\"ENGINEERING_TEST_EVIDENCE_FAILED \",\"plan_diagnostic_prefix\":\"ENGINEERING_TEST_PLAN_FAILED \",\"tail_field\":\"failure_tail\"}}",
                    "SCOPE_EVENT=push",
                    "SCOPE_STATE=selected",
                    $"SCOPE_BASE={Base}",
                    "SCOPE_CHANGED_COUNT=2",
                    "SCOPE_SELECTED_COUNT=1",
                    "SCOPE_FALLBACK_COUNT=0",
                    "PLAN_ARTIFACT_OUTCOME=success",
                    "/bin/bash",
                    scriptPath,
                    action,
                ],
                temporary.Path,
                TestBudgets.ScriptProcessHangGuard,
                128 * 1024);

        private void WriteExecutable(string name, string body)
        {
            if (OperatingSystem.IsWindows()) return;
            ScriptHarnessScratch.WriteExecutableStub(Path.Combine(binPath, name), body);
        }

        public void Dispose() => temporary.Dispose();
    }
}
