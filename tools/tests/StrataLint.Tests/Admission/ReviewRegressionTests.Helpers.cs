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
            var workflowDirectory = Path.Combine(repositoryRoot, ".github", "workflows");
            Directory.CreateDirectory(workflowDirectory);
            File.Copy(
                Path.Combine(FindRepositoryRoot(), ".github", "workflows", "ci.yml"),
                Path.Combine(workflowDirectory, "ci.yml"));
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

    private static string FindRepositoryRoot()
    {
        var directory = new DirectoryInfo(AppContext.BaseDirectory);
        while (directory is not null)
        {
            if (File.Exists(Path.Combine(directory.FullName, ".github", "workflows", "ci.yml")))
            {
                return directory.FullName;
            }

            directory = directory.Parent;
        }

        throw new DirectoryNotFoundException("could not locate repository root");
    }

}
