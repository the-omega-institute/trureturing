using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

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
        TestGit.Run(remoteRoot, "init", "--bare", "--initial-branch=dev");
        TestGit.Run(repositoryRoot, "init", "--initial-branch=dev");
        TestGit.Run(repositoryRoot, "config", "user.email", "stratalint@example.invalid");
        TestGit.Run(repositoryRoot, "config", "user.name", "StrataLint Tests");
        File.WriteAllText(
            Path.Combine(repositoryRoot, "README.md"),
            "# topology fixture\n",
            new UTF8Encoding(false));
        if (installWorkflow)
        {
            // 合成夹具,不复制真实 workflow:被测的是 AdmissionTopology 的判据
            // (on.pull_request.branches 含默认分支,且 jobs 有 delta),
            // 不是仓库 workflow 长什么样。对 workflow 的测试已被永久禁止,见
            // WorkflowTestProhibitionTests。
            var workflowDirectory = Path.Combine(repositoryRoot, ".github", "workflows");
            Directory.CreateDirectory(workflowDirectory);
            File.WriteAllText(
                Path.Combine(workflowDirectory, "ci-pr.yml"),
                "on:\n  pull_request:\n    branches: [dev]\njobs:\n  delta:\n"
                + "    runs-on: ubuntu-latest\n    steps:\n      - run: 'true'\n",
                new UTF8Encoding(false));
        }

        TestGit.Run(repositoryRoot, "add", ".");
        TestGit.Run(repositoryRoot, "commit", "-m", "default branch fixture");
        TestGit.Run(repositoryRoot, "remote", "add", "origin", remoteRoot);
        TestGit.Run(repositoryRoot, "push", "--set-upstream", "origin", "dev");
    }
}
