using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class PureRevertDetectScriptTests
{
    private const string DefaultExecutablePath = "/usr/bin:/bin:/usr/sbin:/sbin";

    private static ProcessOutput Run(
        IReadOnlyList<string> arguments,
        string? executablePath = null)
    {
        var root = TestRepositoryLayout.FindRoot();
        var script = Path.Combine(
            root,
            "tools",
            "scripts",
            "workflow",
            "pure-revert-detect.sh");
        var path = executablePath is null
            ? DefaultExecutablePath
            : executablePath + ":" + DefaultExecutablePath;
        return TestProcessRunner.Run(
            "/usr/bin/env",
            [
                .. IsolatedEnvironmentArguments([], path),
                "/bin/bash",
                script,
                .. arguments,
            ],
            TestScratchRoot.Current.Path,
            TestBudgets.ScriptProcessHangGuard,
            64 * 1024);
    }

    private static void AssertRejected(ProcessOutput result, string reason)
    {
        Assert.NotEqual(0, result.ExitCode);
        Assert.Empty(result.StandardOutput);
        Assert.Equal(reason + "\n", Encoding.UTF8.GetString(result.StandardError));
    }

    private sealed record FileMutation(string Path, string? Content, bool Executable = false);

    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    private sealed class GitFixture : IDisposable
    {
        private readonly TemporaryDirectory temporary = new();

        internal GitFixture()
        {
            Repository = Path.Combine(temporary.Path, "repository");
            ScriptHarnessScratch.EnsureDirectory(Repository);
            Git("init", "-b", "main");
            ConfigureRepository();
            CommitFiles(
                "fixture root",
                new FileMutation(".fixture-root", "root\n"));
            RootSha = Head();
        }

        internal string Repository { get; }

        internal string RootSha { get; }

        internal string BaseSha => GitText("rev-parse", "HEAD^1");

        internal string HeadSha => Head();

        internal string Head() => GitText("rev-parse", "HEAD");

        internal string CommitFiles(string message, params FileMutation[] mutations)
        {
            foreach (var mutation in mutations)
            {
                if (mutation.Content is null)
                {
                    Git("update-index", "--force-remove", "--", mutation.Path);
                    continue;
                }

                var blob = GitTextWithInput(
                    mutation.Content,
                    "hash-object",
                    "-w",
                    "--stdin");
                var mode = mutation.Executable ? "100755" : "100644";
                Git(
                    "update-index",
                    "--add",
                    "--cacheinfo",
                    $"{mode},{blob},{mutation.Path}");
            }

            Git("commit", "-m", message);
            Git("reset", "--hard", "HEAD");
            return Head();
        }

        internal string CommitOnBranch(
            string branch,
            string message,
            params FileMutation[] mutations)
        {
            Git("checkout", "-b", branch);
            var commit = CommitFiles(message, mutations);
            Git("checkout", "main");
            return commit;
        }

        internal string MergeIntoMain(string secondParent, string message) =>
            MergeTreeIntoMain(secondParent, secondParent, message);

        internal string MergeTreeIntoMain(
            string secondParent,
            string treeSource,
            string message)
        {
            var firstParent = Head();
            var tree = GitText("rev-parse", treeSource + "^{tree}");
            var merge = GitText(
                "commit-tree",
                tree,
                "-p",
                firstParent,
                "-p",
                secondParent,
                "-m",
                message);
            Git("update-ref", "refs/heads/main", merge, firstParent);
            Git("reset", "--hard", merge);
            return merge;
        }

        internal void CommitCandidateAndMerge(string message, params FileMutation[] mutations)
        {
            var baseline = Head();
            Git("checkout", "-b", "candidate");
            var candidate = CommitFiles(message, mutations);
            Git("checkout", "main");
            MergeCandidateTree(baseline, candidate, message);
        }

        internal void CommitEmptyCandidateAndMerge(string message)
        {
            var baseline = Head();
            Git("checkout", "-b", "candidate");
            Git("commit", "--allow-empty", "-m", message);
            var candidate = Head();
            Git("checkout", "main");
            MergeCandidateTree(baseline, candidate, message);
        }

        internal string CreateDetachedCommit(string message)
        {
            var tree = GitText("rev-parse", "HEAD^{tree}");
            return GitText("commit-tree", tree, "-m", message);
        }

        internal string CommitGitlink(string message, string path, string target)
        {
            Git("update-index", "--add", "--cacheinfo", $"160000,{target},{path}");
            Git("commit", "-m", message);
            return Head();
        }

        internal void CommitGitlinkCandidateAndMerge(string message, string path, string target)
        {
            var baseline = Head();
            Git("checkout", "-b", "candidate");
            var candidate = CommitGitlink(message, path, target);
            Git("checkout", "main");
            MergeCandidateTree(baseline, candidate, message);
        }

        internal string CreateShallowClone()
        {
            var shallow = Path.Combine(temporary.Path, "shallow");
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                IsolatedGitArguments(
                    ["clone", "--depth=1", new Uri(Repository).AbsoluteUri, shallow]),
                temporary.Path,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return shallow;
        }

        internal void DeleteLooseObject(string sha)
        {
            var objectPath = Path.Combine(
                Repository,
                ".git",
                "objects",
                sha[..2],
                sha[2..]);
            var result = TestProcessRunner.Run(
                "/bin/unlink",
                [objectPath],
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
        }

        internal string CreateFailingGitPath(string failingSubcommand)
        {
            var bin = Path.Combine(temporary.Path, "bin");
            ScriptHarnessScratch.EnsureDirectory(bin);
            ScriptHarnessScratch.WriteExecutableStub(
                Path.Combine(bin, "git"),
                "for argument in \"$@\"; do\n"
                + $"  [[ \"$argument\" != \"{failingSubcommand}\" ]] || exit 91\n"
                + "done\n"
                + "exec /usr/bin/git \"$@\"");
            return bin;
        }

        internal string CreateTimeoutPath(bool expire)
        {
            var bin = Path.Combine(temporary.Path, expire ? "timeout-expire" : "timeout-forward");
            ScriptHarnessScratch.EnsureDirectory(bin);
            var body = expire
                ? "exit 124"
                : "while (( $# > 0 )); do\n"
                    + "  case \"$1\" in\n"
                    + "    --signal=*|--kill-after=*|30s) shift ;;\n"
                    + "    *) break ;;\n"
                    + "  esac\n"
                    + "done\n"
                    + "exec \"$@\"";
            var timeout = Path.Combine(bin, "timeout");
            ScriptHarnessScratch.WriteScratchText(
                timeout,
                "#!/usr/bin/env bash\nset -euo pipefail\n" + body + "\n");
            var chmod = TestProcessRunner.Run(
                "/bin/chmod",
                ["700", timeout],
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(chmod.ExitCode == 0, Diagnostics(chmod));
            return bin;
        }

        internal string ScratchPath(string name) => Path.Combine(temporary.Path, name);

        private void MergeCandidateTree(string baseline, string candidate, string message)
        {
            var tree = GitText("rev-parse", candidate + "^{tree}");
            var merge = GitText(
                "commit-tree",
                tree,
                "-p",
                baseline,
                "-p",
                candidate,
                "-m",
                "merge " + message);
            Git("update-ref", "refs/heads/main", merge, baseline);
            Git("reset", "--hard", merge);
        }

        private void Git(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                IsolatedGitArguments(arguments),
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
        }

        private string GitText(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                IsolatedGitArguments(arguments),
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private string GitTextWithInput(string input, params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/env",
                IsolatedGitArguments(arguments),
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024,
                Encoding.UTF8.GetBytes(input));
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private void ConfigureRepository()
        {
            Git("config", "--local", "user.name", "Pure Revert Test");
            Git("config", "--local", "user.email", "pure-revert@example.invalid");
            Git("config", "--local", "commit.gpgsign", "false");
            Git("config", "--local", "tag.gpgsign", "false");
            Git("config", "--local", "core.autocrlf", "false");
            Git("config", "--local", "core.safecrlf", "false");
            Git("config", "--local", "core.hooksPath", "/dev/null");
            Git("config", "--local", "gc.auto", "0");
            Git("config", "--local", "maintenance.auto", "false");
        }

        public void Dispose() => temporary.Dispose();
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);

    private static string[] IsolatedGitArguments(IEnumerable<string> arguments) =>
        IsolatedEnvironmentArguments(["/usr/bin/git", .. arguments], DefaultExecutablePath);

    private static string[] IsolatedEnvironmentArguments(
        IEnumerable<string> command,
        string path) =>
    [
        "-u", "GIT_AUTHOR_NAME",
        "-u", "GIT_AUTHOR_EMAIL",
        "-u", "GIT_COMMITTER_NAME",
        "-u", "GIT_COMMITTER_EMAIL",
        "-u", "GIT_CONFIG",
        "-u", "GIT_CONFIG_PARAMETERS",
        "-u", "GIT_TEMPLATE_DIR",
        $"PATH={path}",
        "GIT_CONFIG_GLOBAL=/dev/null",
        "GIT_CONFIG_SYSTEM=/dev/null",
        "GIT_CONFIG_NOSYSTEM=1",
        "GIT_CONFIG_COUNT=0",
        .. command,
    ];
}
