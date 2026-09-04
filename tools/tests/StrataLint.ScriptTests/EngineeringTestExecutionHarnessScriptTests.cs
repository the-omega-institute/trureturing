using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EngineeringTestExecutionHarnessScriptTests
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
            $"BASE={run.Base}",
        ],
            run.MakeArguments);
    }

    [Fact]
    public void FullEnvironmentValueIsForwardedWithoutClassification()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(Full: "caller-selected-full-run"));

        Assert.True(run.Process.ExitCode == 0, run.Diagnostics);
        Assert.Equal("set:caller-selected-full-run\n", run.MakeEnvironment);
    }

    [Fact]
    public void AbsentFullEnvironmentRemainsUnsetForMake()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario());

        Assert.True(run.Process.ExitCode == 0, run.Diagnostics);
        Assert.Equal("unset\n", run.MakeEnvironment);
    }

    [Fact]
    public void MissingObservationLibraryEmitsUnavailableAndPreservesMakeExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(
            MakeExitCode: 23,
            ObservationLibraryAvailable: false));

        Assert.Equal(23, run.Process.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason=missing exit=0",
            run.StandardOutput,
            StringComparison.Ordinal);
        Assert.Single(run.MakeArguments, "engineering-tests");
    }

    [Fact]
    public void HeadWithoutFirstParentFailsBeforeMake()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(HeadHasFirstParent: false));

        Assert.Equal(128, run.Process.ExitCode);
        Assert.Contains("HEAD^1", run.StandardError, StringComparison.Ordinal);
        Assert.Empty(run.MakeArguments);
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static HarnessRun RunHarness(HarnessScenario scenario)
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
        var makeEnvironment = Path.Combine(temporary.Path, "make-environment");
        ScriptHarnessScratch.EnsureDirectory(candidateRoot);
        ScriptHarnessScratch.EnsureDirectory(toolsDirectory);
        ScriptHarnessScratch.EnsureDirectory(binDirectory);
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(AppContext.BaseDirectory, "engineering-test-execution-harness.sh"),
            scriptPath);
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(binDirectory, "make"),
            """
            : > "${MAKE_ARGUMENTS:?}"
            for argument in "$@"; do
              printf '%s\n' "$argument" >> "$MAKE_ARGUMENTS"
            done
            if [[ "${FULL+x}" == "x" ]]; then
              printf 'set:%s\n' "$FULL" > "$MAKE_ENVIRONMENT"
            else
              printf '%s\n' 'unset' > "$MAKE_ENVIRONMENT"
            fi
            exit "${MAKE_EXIT_CODE:?}"
            """);
        if (scenario.ObservationLibraryAvailable)
        {
            var observationLibrary = Path.Combine(
                toolsDirectory,
                "scripts",
                "lib",
                "resource-observation-lib.sh");
            ScriptHarnessScratch.EnsureDirectory(Path.GetDirectoryName(observationLibrary)!);
            ScriptHarnessScratch.WriteScratchText(
                observationLibrary,
                "resource_observe_run_periodic() { \"$@\"; }\n");
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

        var repository = GitText(candidateRoot, "rev-parse", "--show-toplevel");
        var head = GitText(candidateRoot, "rev-parse", "HEAD");
        var @base = scenario.HeadHasFirstParent
            ? GitText(candidateRoot, "rev-parse", "HEAD^1")
            : null;
        var environment = new List<string>
        {
            "-u", "FULL",
            "-u", "GIT_CONFIG",
            "-u", "GIT_CONFIG_PARAMETERS",
            $"PATH={binDirectory}:{ExecutablePath}",
            $"TMPDIR={temporary.Path}",
            $"MAKE_ARGUMENTS={makeArguments}",
            $"MAKE_ENVIRONMENT={makeEnvironment}",
            $"MAKE_EXIT_CODE={scenario.MakeExitCode}",
            "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_CONFIG_SYSTEM=/dev/null",
            "GIT_CONFIG_NOSYSTEM=1",
        };
        if (scenario.Full is not null)
        {
            environment.Add($"FULL={scenario.Full}");
        }
        environment.AddRange(["/bin/bash", scriptPath, candidateRoot]);
        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            environment,
            candidateRoot,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
        return new HarnessRun(
            temporary,
            process,
            repository,
            head,
            @base,
            makeArguments,
            makeEnvironment);
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
        string? Full = null,
        bool ObservationLibraryAvailable = true,
        bool HeadHasFirstParent = true);

    private sealed record HarnessRun(
        TemporaryDirectory Temporary,
        ProcessOutput Process,
        string Repository,
        string Head,
        string? Base,
        string MakeArgumentsPath,
        string MakeEnvironmentPath) : IDisposable
    {
        internal string Diagnostics => ProcessDiagnostics(Process);

        internal string StandardOutput => Utf8.GetString(Process.StandardOutput);

        internal string StandardError => Utf8.GetString(Process.StandardError);

        internal string[] MakeArguments =>
            ScriptHarnessScratch.ReadRecordedCalls(MakeArgumentsPath);

        internal string MakeEnvironment =>
            ScriptHarnessScratch.ReadScratchText(MakeEnvironmentPath);

        public void Dispose() => Temporary.Dispose();
    }
}
