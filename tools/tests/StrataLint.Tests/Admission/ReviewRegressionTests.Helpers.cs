using System.Diagnostics;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

/// Asserting the outcome type alone reports which case was returned but not why. A
/// registry that fails to load carries its reason in InfrastructureFailure.Message --
/// for example the exact canonical-order violation in domains.yaml -- and a bare
/// Assert.IsType discards it, leaving a reader with "expected Accepted, got
/// InfrastructureFailure" and no path to the cause except reading RegistryPolicy.
/// See #993: the judgement is right, the reported material is not the one judged.
public static class RegistryLoadAssert
{
    public static RegistryLoadOutcome.Accepted Accepted(RegistryLoadOutcome outcome) =>
        outcome as RegistryLoadOutcome.Accepted
        ?? throw new Xunit.Sdk.XunitException(
            outcome is RegistryLoadOutcome.InfrastructureFailure failure
                ? $"registry load failed: {failure.Message}"
                : $"registry load returned {outcome.GetType().Name}, expected Accepted");
}

public sealed partial class ReviewRegressionTests
{
    private static ValidatedPolicy AcceptedPolicy(string registry)
    {
        var outcome = RegistryLoader.Load(
            Encoding.UTF8.GetBytes(registry),
            Encoding.UTF8.GetBytes(TestRegistry.Domains));
        return RegistryLoadAssert.Accepted(outcome).Policy;
    }

    private static RawRepositorySnapshot Snapshot(IReadOnlyDictionary<string, string> files) =>
        RawRepositorySnapshot.Create(files.Select(pair => RawRepositoryEntry.FromText(pair.Key, pair.Value)));

    private static int Count(string value, string fragment) =>
        (value.Length - value.Replace(fragment, string.Empty, StringComparison.Ordinal).Length) / fragment.Length;

    private static void InitializeRemoteDefaultBranch(
        string remoteRoot,
        string repositoryRoot,
        bool installWorkflow)
    {
        RunGit(remoteRoot, "init", "--bare", "--initial-branch=dev");
        RunGit(repositoryRoot, "init", "--initial-branch=dev");
        RunGit(repositoryRoot, "config", "user.email", "stratalint@example.invalid");
        RunGit(repositoryRoot, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(
            Path.Combine(repositoryRoot, "README.md"),
            "# topology fixture\n",
            new UTF8Encoding(false));
        if (installWorkflow)
        {
            // 合成夹具,不复制真实 workflow:被测的是 AdmissionTopology 的判据
            // (on.pull_request_target.branches 含默认分支,且 jobs 有 baseline-admission),
            // 不是仓库 workflow 长什么样。对 workflow 的测试已被永久禁止,见
            // WorkflowTestProhibitionTests。
            var workflowDirectory = Path.Combine(repositoryRoot, ".github", "workflows");
            Directory.CreateDirectory(workflowDirectory);
            File.WriteAllText(
                Path.Combine(workflowDirectory, "ci.yml"),
                "on:\n  pull_request_target:\n    branches: [dev]\njobs:\n  baseline-admission:\n"
                + "    runs-on: ubuntu-latest\n    steps:\n      - run: 'true'\n",
                new UTF8Encoding(false));
        }

        RunGit(repositoryRoot, "add", ".");
        RunGit(repositoryRoot, "commit", "-m", "default branch fixture");
        RunGit(repositoryRoot, "remote", "add", "origin", remoteRoot);
        RunGit(repositoryRoot, "push", "--set-upstream", "origin", "dev");
    }

    internal static string RunGit(string root, params string[] arguments)
    {
        var requestedBranch = RequestedInitialBranch(arguments);
        var gitArguments = CanonicalGitArguments(arguments);
        var startInfo = new ProcessStartInfo("/usr/bin/env")
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in IsolatedGitArguments(gitArguments))
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = Process.Start(startInfo) ?? throw new InvalidOperationException("git did not start");
        var stdout = process.StandardOutput.ReadToEnd();
        var stderr = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, $"git {string.Join(' ', arguments)} failed: {stderr}");
        if (arguments.Length > 0 && arguments[0] == "init")
        {
            ConfigureSyntheticRepository(root);
            if (requestedBranch is not null && requestedBranch != "main")
            {
                RunGit(root, "symbolic-ref", "HEAD", $"refs/heads/{requestedBranch}");
            }
        }
        return stdout;
    }

    private static string[] CanonicalGitArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 0 || arguments[0] != "init") return arguments.ToArray();
        var result = new List<string> { "init", "--template=", "-b", "main" };
        for (var index = 1; index < arguments.Count; index++)
        {
            var argument = arguments[index];
            if (argument is "-b" or "--initial-branch")
            {
                index++;
                continue;
            }
            if (argument.StartsWith("--initial-branch=", StringComparison.Ordinal)) continue;
            result.Add(argument);
        }
        return result.ToArray();
    }

    private static string? RequestedInitialBranch(IReadOnlyList<string> arguments)
    {
        for (var index = 1; index < arguments.Count; index++)
        {
            if (arguments[index] is "-b" or "--initial-branch")
            {
                return index + 1 < arguments.Count ? arguments[index + 1] : null;
            }
            const string prefix = "--initial-branch=";
            if (arguments[index].StartsWith(prefix, StringComparison.Ordinal))
            {
                return arguments[index][prefix.Length..];
            }
        }
        return null;
    }

    private static void ConfigureSyntheticRepository(string repository)
    {
        RunGit(repository, "config", "--local", "user.name", "StrataLint Tests");
        RunGit(repository, "config", "--local", "user.email", "stratalint@example.invalid");
        RunGit(repository, "config", "--local", "commit.gpgsign", "false");
        RunGit(repository, "config", "--local", "tag.gpgsign", "false");
        RunGit(repository, "config", "--local", "core.autocrlf", "false");
        RunGit(repository, "config", "--local", "core.safecrlf", "false");
        RunGit(repository, "config", "--local", "core.hooksPath", "/dev/null");
        RunGit(repository, "config", "--local", "gc.auto", "0");
        RunGit(repository, "config", "--local", "maintenance.auto", "false");
    }

    private static string[] IsolatedGitArguments(IEnumerable<string> arguments) =>
    [
        "-u", "GIT_AUTHOR_NAME",
        "-u", "GIT_AUTHOR_EMAIL",
        "-u", "GIT_COMMITTER_NAME",
        "-u", "GIT_COMMITTER_EMAIL",
        "-u", "GIT_CONFIG",
        "-u", "GIT_CONFIG_PARAMETERS",
        "-u", "GIT_TEMPLATE_DIR",
        "GIT_CONFIG_GLOBAL=/dev/null",
        "GIT_CONFIG_SYSTEM=/dev/null",
        "GIT_CONFIG_NOSYSTEM=1",
        "GIT_CONFIG_COUNT=0",
        "/usr/bin/git",
        .. arguments,
    ];

}
