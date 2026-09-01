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
        var startInfo = new ProcessStartInfo("git")
        {
            WorkingDirectory = root,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
        };
        foreach (var argument in arguments)
        {
            startInfo.ArgumentList.Add(argument);
        }

        using var process = Process.Start(startInfo) ?? throw new InvalidOperationException("git did not start");
        var stdout = process.StandardOutput.ReadToEnd();
        var stderr = process.StandardError.ReadToEnd();
        process.WaitForExit();
        Assert.True(process.ExitCode == 0, $"git {string.Join(' ', arguments)} failed: {stderr}");
        return stdout;
    }


}
