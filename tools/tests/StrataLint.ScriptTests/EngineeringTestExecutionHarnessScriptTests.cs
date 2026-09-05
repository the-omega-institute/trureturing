using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class EngineeringTestExecutionHarnessScriptTests
{
    private const string ExecutablePath = "/usr/bin:/bin:/usr/sbin:/sbin";
    private static readonly UTF8Encoding Utf8 = new(false);

    [Fact]
    public void CanonicalEngineeringScriptReceivesRepositoryRevisionsDirectly()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario());

        Assert.True(run.Process.ExitCode == 0, run.Diagnostics);
        Assert.Equal(
        [
            run.Repository,
            run.Head,
            run.Base!,
        ],
            run.EngineeringArguments);
    }

    [Fact]
    public void MissingObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.Missing,
            "missing");
    }

    [Fact]
    public void NotRegularObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.NotRegular,
            "not-regular");
    }

    [Fact]
    public void UnreadableObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.Unreadable,
            "unreadable");
    }

    [Fact]
    public void SyntaxInvalidObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.SyntaxInvalid,
            "syntax-error");
    }

    [Fact]
    public void SourceNonzeroObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.SourceNonzero,
            "source-nonzero");
    }

    [Fact]
    public void EntrypointMissingObservationLibraryEmitsUnavailableAndPreservesEngineeringExitCode()
    {
        if (OperatingSystem.IsWindows()) return;
        AssertUnavailableAndPreservesEngineeringExitCodes(
            ObservationLibraryState.EntrypointMissing,
            "entrypoint-missing");
    }

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private static void AssertUnavailableAndPreservesEngineeringExitCodes(
        ObservationLibraryState observationLibraryState,
        string expectedReason)
    {
        foreach (var engineeringExitCode in new[] { 7, 0 })
        {
            using var run = RunHarness(new HarnessScenario(
                EngineeringExitCode: engineeringExitCode,
                ObservationLibraryState: observationLibraryState));

            Assert.True(run.Process.ExitCode == engineeringExitCode, run.Diagnostics);
            Assert.Contains(
                $"RESOURCE_OBSERVATION_LOADER status=UNAVAILABLE reason={expectedReason}",
                run.StandardOutput,
                StringComparison.Ordinal);
            Assert.Equal(3, run.EngineeringArguments.Length);
        }
    }

    [Fact]
    public void HeadWithoutFirstParentFailsBeforeMake()
    {
        if (OperatingSystem.IsWindows()) return;
        using var run = RunHarness(new HarnessScenario(HeadHasFirstParent: false));

        Assert.Equal(128, run.Process.ExitCode);
        Assert.Contains("HEAD^1", run.StandardError, StringComparison.Ordinal);
        Assert.Empty(run.EngineeringArguments);
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
        var engineeringArguments = Path.Combine(temporary.Path, "engineering-arguments");
        ScriptHarnessScratch.EnsureDirectory(candidateRoot);
        ScriptHarnessScratch.EnsureDirectory(toolsDirectory);
        ScriptHarnessScratch.EnsureDirectory(binDirectory);
        ScriptHarnessScratch.CopyScriptInto(
            Path.Combine(AppContext.BaseDirectory, "engineering-test-execution-harness.sh"),
            scriptPath);
        ScriptHarnessScratch.WriteExecutableStub(
            Path.Combine(toolsDirectory, "scripts", "engineering-tests.sh"),
            """
            : > "${ENGINEERING_ARGUMENTS:?}"
            for argument in "$@"; do
              printf '%s\n' "$argument" >> "$ENGINEERING_ARGUMENTS"
            done
            exit "${ENGINEERING_EXIT_CODE:?}"
            """);
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
                        "resource_observe_run_periodic() { \"$@\"; }\n",
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
        var environment = new List<string>
        {
            "-u", "GIT_CONFIG",
            "-u", "GIT_CONFIG_PARAMETERS",
            $"PATH={binDirectory}:{ExecutablePath}",
            $"TMPDIR={temporary.Path}",
            $"ENGINEERING_ARGUMENTS={engineeringArguments}",
            $"ENGINEERING_EXIT_CODE={scenario.EngineeringExitCode}",
            "GIT_CONFIG_GLOBAL=/dev/null",
            "GIT_CONFIG_SYSTEM=/dev/null",
            "GIT_CONFIG_NOSYSTEM=1",
        };
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
            engineeringArguments);
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
        int EngineeringExitCode = 0,
        ObservationLibraryState ObservationLibraryState = ObservationLibraryState.Available,
        bool HeadHasFirstParent = true);

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
        string EngineeringArgumentsPath) : IDisposable
    {
        internal string Diagnostics => ProcessDiagnostics(Process);

        internal string StandardOutput => Utf8.GetString(Process.StandardOutput);

        internal string StandardError => Utf8.GetString(Process.StandardError);

        internal string[] EngineeringArguments =>
            ScriptHarnessScratch.ReadRecordedCalls(EngineeringArgumentsPath);

        public void Dispose() => Temporary.Dispose();
    }

}
