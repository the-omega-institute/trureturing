using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class EngineeringTestExecutionHarnessScriptTests
{
    private const string HarnessPath =
        "tools/scripts/workflow/engineering-test-execution-harness.sh";
    private static readonly UTF8Encoding Utf8 = new(false);

    [Fact]
    public void FullEnvironmentReachesEngineeringTestTargetWithCanonicalArguments()
    {
        var result = RunHarness(engineeringExitCode: 0, full: "1");

        Assert.True(result.ExitCode == 0, result.Diagnostics);
        Assert.Contains(
            result.ExpectedInvocation(full: "1"),
            result.StandardOutput,
            StringComparison.Ordinal);
    }

    [Fact]
    public void AbsentFullEnvironmentKeepsScopedEngineeringTestTarget()
    {
        var result = RunHarness(engineeringExitCode: 0);

        Assert.True(result.ExitCode == 0, result.Diagnostics);
        Assert.Contains(
            result.ExpectedInvocation(full: "unset"),
            result.StandardOutput,
            StringComparison.Ordinal);
    }

    [Fact]
    public void PeriodicObservationFailureDoesNotChangeEngineeringTestExitCode()
    {
        var result = RunHarness(engineeringExitCode: 23);

        Assert.Equal(2, result.ExitCode);
        Assert.Contains(
            "RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=97",
            result.StandardOutput,
            StringComparison.Ordinal);
        Assert.Contains(
            result.ExpectedInvocation(full: "unset"),
            result.StandardOutput,
            StringComparison.Ordinal);
    }

    private static HarnessResult RunHarness(int engineeringExitCode, string? full = null)
    {
        using var temporary = new TemporaryDirectory();
        var repositoryRoot = TestRepositoryLayout.FindRoot();
        var candidateRoot = Path.Combine(temporary.Path, "candidate");
        Directory.CreateDirectory(candidateRoot);

        WriteFile(
            candidateRoot,
            HarnessPath,
            File.ReadAllText(Path.Combine(repositoryRoot, HarnessPath), Utf8));
        WriteFile(
            candidateRoot,
            "tools/scripts/lib/resource-observation-lib.sh",
            """
            resource_observe_run_periodic() {
              local command_status=0
              set +e
              "$@"
              command_status=$?
              set -e
              printf '%s\n' 'RESOURCE_OBSERVATION_SAMPLER status=UNAVAILABLE exit=97'
              return "$command_status"
            }
            """);
        WriteFile(
            candidateRoot,
            "tools/Makefile",
            ".PHONY: engineering-tests\n"
            + "engineering-tests:\n"
            + "\t@printf 'ENGINEERING_TEST_CALL repository=%s head=%s base=%s full=%s\\n' \"$(REPOSITORY)\" \"$(HEAD)\" \"$(BASE)\" \"$${FULL-unset}\"\n"
            + "\t@exit \"$${ENGINEERING_TEST_FAKE_EXIT:?}\"\n");

        RunGit(candidateRoot, "init", "--quiet");
        RunGit(candidateRoot, "config", "user.email", "engineering-harness@example.invalid");
        RunGit(candidateRoot, "config", "user.name", "Engineering Harness Tests");
        RunGit(candidateRoot, "add", ".");
        RunGit(candidateRoot, "commit", "--quiet", "-m", "base");
        WriteFile(candidateRoot, "content/change.md", "candidate change\n");
        RunGit(candidateRoot, "add", ".");
        RunGit(candidateRoot, "commit", "--quiet", "-m", "candidate");

        var head = GitText(candidateRoot, "rev-parse", "HEAD");
        var @base = GitText(candidateRoot, "rev-parse", "HEAD^1");
        var environment = new List<string>
        {
            "-u",
            "FULL",
            $"GITHUB_WORKSPACE={temporary.Path}",
            $"ENGINEERING_TEST_FAKE_EXIT={engineeringExitCode}",
        };
        if (full is not null)
        {
            environment.Add($"FULL={full}");
        }
        environment.AddRange(
        [
            "/bin/bash",
            Path.Combine(candidateRoot, HarnessPath),
            candidateRoot,
        ]);
        var process = TestProcessRunner.Run(
            "/usr/bin/env",
            environment,
            candidateRoot,
            TestBudgets.ScriptProcessHangGuard,
            1024 * 1024);
        return new HarnessResult(
            process.ExitCode,
            Utf8.GetString(process.StandardOutput),
            Utf8.GetString(process.StandardError),
            GitText(candidateRoot, "rev-parse", "--show-toplevel"),
            head,
            @base);
    }

    private static void WriteFile(string root, string path, string contents)
    {
        var fullPath = Path.Combine(root, path);
        Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
        File.WriteAllText(fullPath, contents + (contents.EndsWith('\n') ? "" : "\n"), Utf8);
    }

    private static string GitText(string root, params string[] arguments) =>
        RunGit(root, arguments).Trim();

    private static string RunGit(string root, params string[] arguments)
    {
        var result = TestProcessRunner.Run(
            "git",
            arguments,
            root,
            TestBudgets.ScriptProcessHangGuard,
            1024 * 1024);
        var output = Utf8.GetString(result.StandardOutput);
        var error = Utf8.GetString(result.StandardError);
        Assert.True(
            result.ExitCode == 0,
            $"git {string.Join(' ', arguments)} exited {result.ExitCode}: {error}");
        return output;
    }

    private sealed record HarnessResult(
        int ExitCode,
        string StandardOutput,
        string StandardError,
        string CandidateRoot,
        string Head,
        string Base)
    {
        internal string Diagnostics =>
            $"exit={ExitCode}; stdout={StandardOutput}; stderr={StandardError}";

        internal string ExpectedInvocation(string full) =>
            $"ENGINEERING_TEST_CALL repository={CandidateRoot} head={Head} base={Base} full={full}";
    }
}
