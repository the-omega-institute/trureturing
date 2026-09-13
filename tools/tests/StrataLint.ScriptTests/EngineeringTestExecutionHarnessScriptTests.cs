using System.Text;
using System.Text.Json;
using StrataLint.Engine;
using Xunit.Abstractions;

namespace StrataLint.Tests;

public sealed class EngineeringTestExecutionHarnessScriptTests(ITestOutputHelper output)
{
    private const string ExecutablePath = "/usr/bin:/bin:/usr/sbin:/sbin";
    private static readonly UTF8Encoding Utf8 = new(false);

    [Fact]
    public void CanonicalMakeInvocationPassesEngineeringTargetAndRepositoryRevisions()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario());

        Assert.True(run.Process.ExitCode == 0, run.Diagnostics);
        Assert.Equal(
        [
            "--no-print-directory",
            "-C",
            Path.Combine(run.Repository, "tools"),
            "engineering-tests",
            $"REPOSITORY={run.Repository}",
            $"HEAD={run.Head}",
            $"EVENT=push",
            $"BEFORE={run.Base}",
        ],
            run.MakeArguments);
    }

    [Fact]
    public void MissingObservationLibraryEmitsUnavailableAndPreservesMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesMakeExitCodes(
            ObservationLibraryState.Missing,
            "missing");
    }

    [Fact]
    public void NotRegularObservationLibraryEmitsUnavailableAndPreservesMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesMakeExitCodes(
            ObservationLibraryState.NotRegular,
            "not-regular");
    }

    [Fact]
    public void UnreadableObservationLibraryEmitsUnavailableAndPreservesMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesMakeExitCodes(
            ObservationLibraryState.Unreadable,
            "unreadable");
    }

    [Fact]
    public void SyntaxInvalidObservationLibraryEmitsUnavailableAndPreservesMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesMakeExitCodes(
            ObservationLibraryState.SyntaxInvalid,
            "syntax-error");
    }

    [Fact]
    public void SourceNonzeroObservationLibraryEmitsUnavailableAndPreservesMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesMakeExitCodes(
            ObservationLibraryState.SourceNonzero,
            "source-nonzero");
    }

    [Fact]
    public void EntrypointMissingObservationLibraryEmitsUnavailableAndPreservesMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesMakeExitCodes(
            ObservationLibraryState.EntrypointMissing,
            "entrypoint-missing");
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private void AssertUnavailableAndPreservesMakeExitCodes(
        ObservationLibraryState observationLibraryState,
        string expectedReason)
    {
        foreach (var makeExitCode in new[] { 7, 0 })
        {
            using var run = RunHarness(new HarnessScenario(
                MakeExitCode: makeExitCode,
                ObservationLibraryState: observationLibraryState));

            Assert.True(run.Process.ExitCode == makeExitCode, run.Diagnostics);
            Assert.Contains(
                $"RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason={expectedReason}",
                run.StandardOutput,
                StringComparison.Ordinal);
            Assert.Single(run.MakeArguments, "engineering-tests");
        }
    }

    [Fact]
    public void InitialPushWithoutFirstParentPassesExplicitZeroBefore()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(HeadHasFirstParent: false));

        Assert.Equal(0, run.Process.ExitCode);
        Assert.Contains("BEFORE=" + new string('0', 40), run.MakeArguments);
    }

    [Theory]
    [InlineData("pull_request")]
    [InlineData("pull_request_target")]
    public void OneRootPullRequestEntryUsesCheckedMergeParent(string eventName)
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(EventName: eventName));

        Assert.True(run.Process.ExitCode == 0, run.Diagnostics);
        Assert.Equal(
        [
            "--no-print-directory", "-C", Path.Combine(run.Repository, "tools"),
            "engineering-tests", $"REPOSITORY={run.Repository}", $"HEAD={run.Head}",
            "EVENT=pull-request", $"BASE={run.Base}",
        ], run.MakeArguments);
        Assert.Contains("CI_CHECKED_IDENTITY ", run.StandardError, StringComparison.Ordinal);
        var identityLine = Assert.Single(run.StandardError.Split('\n'),
            line => line.StartsWith("CI_CHECKED_IDENTITY ", StringComparison.Ordinal));
        using var identity = JsonDocument.Parse(identityLine["CI_CHECKED_IDENTITY ".Length..]);
        Assert.Equal(run.Head, identity.RootElement.GetProperty("tested_head").GetString());
        Assert.Equal(run.Base, identity.RootElement.GetProperty("protected_base").GetString());
        // The event base can advance separately from the checked merge's first parent.
        Assert.NotEqual(run.Base, identity.RootElement.GetProperty("event_pr_base").GetString());
        Assert.Equal(eventName == "pull_request", identity.RootElement.GetProperty("candidate_workflow").GetBoolean());
        if (eventName == "pull_request_target")
            Assert.NotEqual(run.Head, identity.RootElement.GetProperty("event_sha").GetString());
    }

    [Theory]
    [InlineData("multicommit")]
    [InlineData("nonancestor")]
    [InlineData("initial")]
    public void OneRootPushEntryPreservesFullExplicitEndpoints(string change)
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(Change: change));

        Assert.True(run.Process.ExitCode == 0, run.Diagnostics);
        Assert.Contains($"HEAD={run.Head}", run.MakeArguments);
        Assert.Contains("EVENT=push", run.MakeArguments);
        Assert.Contains($"BEFORE={run.Before}", run.MakeArguments);
        Assert.DoesNotContain(run.MakeArguments, argument => argument.StartsWith("BASE=", StringComparison.Ordinal));
        Assert.NotEqual(GitText(run.Repository, "rev-parse", "HEAD^1"), run.Before);
    }

    [Theory]
    [InlineData("push", "missing-event", "missing GITHUB_EVENT_NAME")]
    [InlineData("push", "missing-payload", "missing GITHUB_EVENT_PATH")]
    [InlineData("push", "invalid-json", "CI_CHECKED_IDENTITY_INVALID")]
    [InlineData("push", "missing-before", "'before'")]
    [InlineData("push", "malformed-before", "complete fixed object IDs")]
    [InlineData("push", "missing-object", "missing pinned push before commit")]
    [InlineData("push", "noncommit-before", "missing pinned push before commit")]
    [InlineData("push", "wrong-after", "event.after differs from checkout HEAD")]
    [InlineData("push", "wrong-head", "event must name the checked commit")]
    [InlineData("push", "deleted", "deletion event has no candidate")]
    [InlineData("push", "zero-without-created", "zero before requires an initial branch event")]
    [InlineData("push", "created-without-zero", "zero before requires an initial branch event")]
    [InlineData("push", "invalid-created", "created/deleted must be booleans")]
    [InlineData("push", "invalid-deleted", "created/deleted must be booleans")]
    [InlineData("push", "missing-workflow", "missing GITHUB_WORKFLOW_SHA")]
    [InlineData("push", "malformed-workflow", "invalid GITHUB_WORKFLOW_SHA")]
    [InlineData("push", "missing-run", "missing GITHUB_RUN_ID")]
    [InlineData("pull_request", "wrong-head", "event must name the checked commit")]
    [InlineData("pull_request", "wrong-parent", "second parent differs from event PR head")]
    [InlineData("pull_request", "default-workflow", "PR workflow must name the checked commit")]
    [InlineData("pull_request_target", "wrong-parent", "second parent differs from event PR head")]
    [InlineData("schedule", "valid", "unsupported event schedule")]
    public void InvalidEventFailsBeforeObservationOrMake(string eventName, string change, string diagnostic)
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(EventName: eventName, Change: change));

        Assert.True(run.Process.ExitCode == 2, run.Diagnostics);
        Assert.Contains("CI_CHECKED_IDENTITY_INVALID", run.StandardError, StringComparison.Ordinal);
        Assert.Contains(diagnostic, run.StandardError, StringComparison.Ordinal);
        Assert.Empty(run.MakeArguments);
        Assert.DoesNotContain("OBSERVATION_CALLED", run.StandardOutput, StringComparison.Ordinal);
    }

    [Fact]
    public void FourArgumentEntryIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(AdditionalArguments: true));

        Assert.True(run.Process.ExitCode == 2, run.Diagnostics);
        Assert.Contains("usage:", run.StandardError, StringComparison.Ordinal);
        Assert.Empty(run.MakeArguments);
        Assert.DoesNotContain("OBSERVATION_CALLED", run.StandardOutput, StringComparison.Ordinal);
    }

    [Fact]
    public void AvailableObservationPreservesNonzeroMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(MakeExitCode: 7));

        Assert.True(run.Process.ExitCode == 7, run.Diagnostics);
        Assert.Contains("OBSERVATION_CALLED", run.StandardOutput, StringComparison.Ordinal);
        Assert.Single(run.MakeArguments, "engineering-tests");
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private HarnessRun RunHarness(HarnessScenario scenario)
    {
        var temporary = new TemporaryDirectory();
        var candidateRoot = Path.Combine(temporary.Path, "candidate");
        var toolsDirectory = Path.Combine(candidateRoot, "tools");
        var scriptPath = Path.Combine(
            toolsDirectory,
            "scripts",
            "workflow",
            "engineering-test-execution-harness.sh");
        var binDirectory = Path.Combine(temporary.Path, "bin");
        var makeArguments = Path.Combine(temporary.Path, "make-arguments");
        ScriptHarnessScratch.EnsureDirectory(candidateRoot);
        ScriptHarnessScratch.EnsureDirectory(toolsDirectory);
        ScriptHarnessScratch.EnsureDirectory(binDirectory);
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(AppContext.BaseDirectory, "engineering-test-execution-harness.sh"),
            scriptPath);
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(TestRepositoryLayout.FindRoot(), "tools/scripts/workflow/checked-ci-identity.py"),
            Path.Combine(Path.GetDirectoryName(scriptPath)!, "checked-ci-identity.py"));
        File.WriteAllText(
            Path.Combine(binDirectory, "make"),
            """
            #!/usr/bin/env bash
            set -euo pipefail
            : > "${MAKE_ARGUMENTS:?}"
            for argument in "$@"; do
              printf '%s\n' "$argument" >> "$MAKE_ARGUMENTS"
            done
            exit "${MAKE_EXIT_CODE:?}"
            """, Utf8);
        File.SetUnixFileMode(Path.Combine(binDirectory, "make"),
            UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
        var observationLibrary = Path.Combine(
            toolsDirectory,
            "scripts",
            "lib",
            "resource-observation-lib.sh");
        if (scenario.ObservationLibraryState == ObservationLibraryState.NotRegular)
        {
            ScriptHarnessScratch.EnsureDirectory(observationLibrary);
        }
        else if (scenario.ObservationLibraryState != ObservationLibraryState.Missing)
        {
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(observationLibrary)!);
            ScriptHarnessScratch.WriteScratchText(
                observationLibrary,
                scenario.ObservationLibraryState switch
                {
                    ObservationLibraryState.Available =>
                        "resource_observe_run_periodic() { echo OBSERVATION_CALLED; \"$@\"; }\n",
                    ObservationLibraryState.Unreadable =>
                        "resource_observe_run_periodic() { \"$@\"; }\n",
                    ObservationLibraryState.SyntaxInvalid =>
                        "resource_observe_run_periodic() {\n",
                    ObservationLibraryState.SourceNonzero => "return 41\n",
                    ObservationLibraryState.EntrypointMissing => ":\n",
                    _ => throw new InvalidOperationException(
                        $"Unsupported observation library state: {scenario.ObservationLibraryState}"),
                });
        }

        RunGit(candidateRoot, "init", "--quiet");
        RunGit(candidateRoot, "config", "user.email", "engineering-harness@example.invalid");
        RunGit(candidateRoot, "config", "user.name", "Engineering Harness Tests");
        RunGit(candidateRoot, "config", "commit.gpgsign", "false");
        RunGit(candidateRoot, "config", "core.hooksPath", "/dev/null");
        RunGit(candidateRoot, "add", ".");
        RunGit(candidateRoot, "commit", "--quiet", "-m", "fixture root");
        if (scenario.HeadHasFirstParent)
        {
            ScriptHarnessScratch.WriteScratchText(
                Path.Combine(candidateRoot, "candidate-change.txt"),
                "candidate change\n");
            RunGit(candidateRoot, "add", ".");
            RunGit(candidateRoot, "commit", "--quiet", "-m", "candidate");
        }
        if (scenario.ObservationLibraryState == ObservationLibraryState.Unreadable)
        {
            File.SetUnixFileMode(observationLibrary, UnixFileMode.None);
        }

        var repository = GitText(candidateRoot, "rev-parse", "--show-toplevel");
        var head = GitText(candidateRoot, "rev-parse", "HEAD");
        var @base = scenario.HeadHasFirstParent
            ? GitText(candidateRoot, "rev-parse", "HEAD^1")
            : null;
        var before = @base ?? new string('0', 40);
        if (scenario.Change == "multicommit")
        {
            RunGit(candidateRoot, "commit", "--quiet", "--allow-empty", "-m", "second pushed commit");
            head = GitText(candidateRoot, "rev-parse", "HEAD");
        }
        if (scenario.Change == "nonancestor")
            before = GitText(candidateRoot, "commit-tree", "HEAD^{tree}", "-m", "nonancestor planning endpoint");
        var prHead = head;
        if (scenario.EventName is "pull_request" or "pull_request_target")
        {
            head = GitText(candidateRoot, "commit-tree", "HEAD^{tree}", "-p", @base!, "-p", prHead, "-m", "checked merge");
            RunGit(candidateRoot, "checkout", "--quiet", "--detach", head);
        }
        var eventPath = Path.Combine(temporary.Path, "event.json");
        var payload = new Dictionary<string, object?>
        {
            ["before"] = before, ["after"] = head,
            ["created"] = !scenario.HeadHasFirstParent, ["deleted"] = false,
            ["pull_request"] = new { head = new { sha = scenario.Change == "wrong-parent" ? @base : prHead },
                @base = new { sha = prHead } },
        };
        var eventEnvironment = new Dictionary<string, string>
        {
            ["GITHUB_EVENT_NAME"] = scenario.EventName, ["GITHUB_EVENT_PATH"] = eventPath,
            ["GITHUB_SHA"] = scenario.EventName == "pull_request_target" ? @base! : head,
            ["GITHUB_WORKFLOW_SHA"] = scenario.EventName == "pull_request_target" ? @base! : head,
            ["GITHUB_WORKFLOW_REF"] = "owner/repo/ci-fixture.yml@refs/heads/dev",
            ["GITHUB_RUN_ID"] = "23", ["GITHUB_RUN_ATTEMPT"] = "1", ["GITHUB_JOB"] = "engineering",
        };
        var eventKeys = eventEnvironment.Keys.ToArray();
        switch (scenario.Change)
        {
            case "initial": before = new string('0', 40); payload["before"] = before; payload["created"] = true; break;
            case "missing-event": eventEnvironment.Remove("GITHUB_EVENT_NAME"); break;
            case "missing-payload": eventEnvironment.Remove("GITHUB_EVENT_PATH"); break;
            case "missing-workflow": eventEnvironment.Remove("GITHUB_WORKFLOW_SHA"); break;
            case "missing-run": eventEnvironment.Remove("GITHUB_RUN_ID"); break;
            case "malformed-workflow": eventEnvironment["GITHUB_WORKFLOW_SHA"] = "dev"; break;
            case "default-workflow": eventEnvironment["GITHUB_WORKFLOW_SHA"] = @base!; break;
            case "wrong-head": eventEnvironment["GITHUB_SHA"] = @base!; break;
            case "missing-before": payload.Remove("before"); break;
            case "malformed-before": payload["before"] = "HEAD^1"; break;
            case "missing-object": payload["before"] = new string('1', 40); break;
            case "noncommit-before": payload["before"] = GitText(candidateRoot, "rev-parse", "HEAD^{tree}"); break;
            case "wrong-after": payload["after"] = @base; break;
            case "deleted": payload["after"] = new string('0', 40); payload["deleted"] = true; break;
            case "zero-without-created": payload["before"] = new string('0', 40); break;
            case "created-without-zero": payload["created"] = true; break;
            case "invalid-created": payload["created"] = "false"; break;
            case "invalid-deleted": payload["deleted"] = 0; break;
        }
        ScriptHarnessScratch.WriteScratchText(eventPath,
            scenario.Change == "invalid-json" ? "{" : JsonSerializer.Serialize(payload));
        var environment = new List<string>
        {
            "-u", "GIT_CONFIG",
            "-u", "GIT_CONFIG_PARAMETERS",
            $"PATH={binDirectory}:{ExecutablePath}",
            $"TMPDIR={temporary.Path}",
            $"MAKE_ARGUMENTS={makeArguments}",
            $"MAKE_EXIT_CODE={scenario.MakeExitCode}",
            "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_CONFIG_SYSTEM=/dev/null",
            "GIT_CONFIG_NOSYSTEM=1",
        };
        // Clear inherited Actions inputs so missing-field fixtures stay missing under CI.
        environment.InsertRange(0, eventKeys.SelectMany(key => new[] { "-u", key }));
        environment.AddRange(eventEnvironment.Select(pair => pair.Key + "=" + pair.Value));
        environment.AddRange(["/bin/bash", scriptPath, candidateRoot]);
        if (scenario.AdditionalArguments) environment.AddRange(["push", before, head]);
        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            environment,
            temporary.Path,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        output.WriteLine("PROGRAM executable=/usr/bin/env cwd=" + temporary.Path
            + " argv=" + JsonSerializer.Serialize(environment) + " exit=" + process.ExitCode
            + "\n" + ProcessDiagnostics(process));
        return new HarnessRun(
            temporary,
            process,
            repository,
            head,
            @base,
            before,
            makeArguments);
    }

    private static void RunGit(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            GitArguments(arguments),
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, ProcessDiagnostics(result));
    }

    private static string GitText(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "/usr/bin/env",
            GitArguments(arguments),
            root,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        Assert.True(result.ExitCode == 0, ProcessDiagnostics(result));
        return Utf8.GetString(result.StandardOutput).Trim();
    }

    private static string[] GitArguments(IEnumerable<string> arguments) =>
    [
        "-u", "GIT_AUTHOR_NAME",
        "-u", "GIT_AUTHOR_EMAIL",
        "-u", "GIT_COMMITTER_NAME",
        "-u", "GIT_COMMITTER_EMAIL",
        "-u", "GIT_CONFIG",
        "-u", "GIT_CONFIG_PARAMETERS",
        "GIT_CONFIG_GLOBAL=/dev/null",
        "GIT_CONFIG_SYSTEM=/dev/null",
        "GIT_CONFIG_NOSYSTEM=1",
        "PATH=" + ExecutablePath,
        "/usr/bin/git",
        .. arguments,
    ];

    private static string ProcessDiagnostics(ProcessOutput process) =>
        "stdout:\n" + Utf8.GetString(process.StandardOutput)
        + "\nstderr:\n" + Utf8.GetString(process.StandardError);

    private sealed record HarnessScenario(
        int MakeExitCode = 0,
        ObservationLibraryState ObservationLibraryState = ObservationLibraryState.Available,
        bool HeadHasFirstParent = true,
        string EventName = "push",
        string Change = "valid",
        bool AdditionalArguments = false);

    private enum ObservationLibraryState
    {
        Available,
        Missing,
        NotRegular,
        Unreadable,
        SyntaxInvalid,
        SourceNonzero,
        EntrypointMissing,
    }

    private sealed record HarnessRun(
        TemporaryDirectory Temporary,
        ProcessOutput Process,
        string Repository,
        string Head,
        string? Base,
        string Before,
        string MakeArgumentsPath) : IDisposable
    {
        internal string Diagnostics => ProcessDiagnostics(Process);

        internal string StandardOutput => Utf8.GetString(Process.StandardOutput);

        internal string StandardError => Utf8.GetString(Process.StandardError);

        internal string[] MakeArguments =>
            ScriptHarnessScratch.ReadRecordedCalls(MakeArgumentsPath);

        public void Dispose() => Temporary.Dispose();
    }
}
