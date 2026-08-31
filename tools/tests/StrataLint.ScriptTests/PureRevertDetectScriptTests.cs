using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class PureRevertDetectScriptTests
{
    [Fact]
    public void ExactToolsOnlyMergeInverseAfterUnrelatedCommitIsAccepted()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed target", new FileMutation("tools/target.txt", "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "target transition",
            new FileMutation("tools/target.txt", "after\n"));
        var target = fixture.MergeIntoMain(feature, "merge target");
        fixture.CommitFiles("later unrelated", new FileMutation("tools/later.txt", "later\n"));
        fixture.CommitCandidateAndMerge(
            "exact inverse",
            new FileMutation("tools/target.txt", "before\n"));

        var result = Run([fixture.Repository]);

        Assert.Equal(0, result.ExitCode);
        Assert.Empty(result.StandardError);
        var output = Encoding.UTF8.GetString(result.StandardOutput);
        Assert.Equal(1, output.Count(static character => character == '\n'));
        Assert.Contains($"base_sha={fixture.BaseSha}", output, StringComparison.Ordinal);
        Assert.Contains($"head_sha={fixture.HeadSha}", output, StringComparison.Ordinal);
        Assert.Contains($"target_merge_sha={target}", output, StringComparison.Ordinal);
        Assert.Contains("changed_path_count=1", output, StringComparison.Ordinal);
    }

    [Fact]
    public void WrongTargetHintCannotOverrideIndependentlyLocatedTarget()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed target", new FileMutation("tools/target.txt", "before\n"));
        var feature = fixture.CommitOnBranch(
            "feature",
            "target transition",
            new FileMutation("tools/target.txt", "after\n"));
        var target = fixture.MergeIntoMain(feature, "merge target");
        fixture.CommitCandidateAndMerge(
            "exact inverse",
            new FileMutation("tools/target.txt", "before\n"));

        var result = Run([fixture.Repository, fixture.RootSha]);

        Assert.Equal(0, result.ExitCode);
        Assert.Contains(
            $"target_merge_sha={target}",
            Encoding.UTF8.GetString(result.StandardOutput),
            StringComparison.Ordinal);
    }

    [Fact]
    public void NoOpMergeResultIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "value\n"));
        fixture.CommitEmptyCandidateAndMerge("no-op candidate");

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NO_CHANGES");
    }

    [Fact]
    public void AncientAncestorTreeRestorationWithoutSingleExactTransitionIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "ancient tree",
            new FileMutation("tools/one.txt", "one-before\n"),
            new FileMutation("tools/two.txt", "two-before\n"));
        fixture.CommitFiles("change one", new FileMutation("tools/one.txt", "one-after\n"));
        fixture.CommitFiles("change two", new FileMutation("tools/two.txt", "two-after\n"));
        fixture.CommitCandidateAndMerge(
            "restore ancient tree",
            new FileMutation("tools/one.txt", "one-before\n"),
            new FileMutation("tools/two.txt", "two-before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void ExactSecondParentTransitionIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        var secondParent = fixture.CommitOnBranch(
            "feature",
            "second parent transition",
            new FileMutation("tools/target.txt", "after\n"));
        var resolutionTree = fixture.CommitOnBranch(
            "resolution-tree",
            "conflict resolution tree",
            new FileMutation("tools/target.txt", "resolution\n"));
        fixture.MergeTreeIntoMain(secondParent, resolutionTree, "merge with resolution");
        fixture.CommitFiles("later target rewrite", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse second parent only",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(
            Run([fixture.Repository, secondParent]),
            "PURE_REVERT_SECOND_PARENT");
    }

    [Fact]
    public void PartialInverseIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed",
            new FileMutation("tools/one.txt", "one-before\n"),
            new FileMutation("tools/two.txt", "two-before\n"));
        fixture.CommitFiles(
            "two-path target",
            new FileMutation("tools/one.txt", "one-after\n"),
            new FileMutation("tools/two.txt", "two-after\n"));
        fixture.CommitCandidateAndMerge(
            "partial inverse",
            new FileMutation("tools/one.txt", "one-before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void InverseWithAdditionalPathIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse plus extra",
            new FileMutation("tools/target.txt", "before\n"),
            new FileMutation("tools/extra.txt", "extra\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void TargetPathModifiedLaterIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "target\n"));
        fixture.CommitFiles("later rewrite", new FileMutation("tools/target.txt", "later\n"));
        fixture.CommitCandidateAndMerge(
            "unclean inverse",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void ExactInverseOutsideCanonicalHarnessAllowlistIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed ledger",
            new FileMutation("Golden/Frozen/accepted/node.json", "before\n"));
        fixture.CommitFiles(
            "ledger target",
            new FileMutation("Golden/Frozen/accepted/node.json", "after\n"));
        fixture.CommitCandidateAndMerge(
            "ledger inverse",
            new FileMutation("Golden/Frozen/accepted/node.json", "before\n"));

        AssertRejected(
            Run([fixture.Repository]),
            "PURE_REVERT_PATH_OUTSIDE_ALLOWLIST");
    }

    [Fact]
    public void BlobRestorationWithoutModeRestorationIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed mode",
            new FileMutation("tools/mode.sh", "before\n", Executable: false));
        fixture.CommitFiles(
            "content and mode target",
            new FileMutation("tools/mode.sh", "after\n", Executable: true));
        fixture.CommitCandidateAndMerge(
            "blob-only inverse",
            new FileMutation("tools/mode.sh", "before\n", Executable: true));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void GitlinkPointerMismatchIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        var first = fixture.CreateDetachedCommit("gitlink one");
        var second = fixture.CreateDetachedCommit("gitlink two");
        var third = fixture.CreateDetachedCommit("gitlink three");
        fixture.CommitGitlink("seed gitlink", "tools/link", first);
        fixture.CommitGitlink("target gitlink", "tools/link", second);
        fixture.CommitGitlinkCandidateAndMerge("wrong gitlink inverse", "tools/link", third);

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void ForgedRevertMessageWithoutInverseTreeIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "Revert \"target\"",
            new FileMutation("tools/target.txt", "forged\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_NOT_INVERSE");
    }

    [Fact]
    public void MultipleExactFirstParentTargetsFailClosedAsAmbiguous()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("first target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitFiles("restore", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("second target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse with two witnesses",
            new FileMutation("tools/target.txt", "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_AMBIGUOUS_TARGET");
    }

    [Fact]
    public void CandidateThatChangesClassifierItselfIsRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles(
            "seed classifier",
            new FileMutation(
                "tools/scripts/workflow/pure-revert-detect.sh",
                "before\n"));
        fixture.CommitFiles(
            "classifier target",
            new FileMutation(
                "tools/scripts/workflow/pure-revert-detect.sh",
                "after\n"));
        fixture.CommitCandidateAndMerge(
            "classifier inverse",
            new FileMutation(
                "tools/scripts/workflow/pure-revert-detect.sh",
                "before\n"));

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_CLASSIFIER_MODIFIED");
    }

    [Fact]
    public void ShallowRepositoryFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse",
            new FileMutation("tools/target.txt", "before\n"));
        var shallow = fixture.CreateShallowClone();

        AssertRejected(Run([shallow]), "PURE_REVERT_HISTORY_UNAVAILABLE");
    }

    [Fact]
    public void MissingFirstParentObjectFailsClosed()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        var missing = fixture.Head();
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse",
            new FileMutation("tools/target.txt", "before\n"));
        fixture.DeleteLooseObject(missing);

        AssertRejected(Run([fixture.Repository]), "PURE_REVERT_HISTORY_UNAVAILABLE");
    }

    [Fact]
    public void MissingArgumentsAreRejected()
    {
        if (OperatingSystem.IsWindows()) return;

        AssertRejected(Run([]), "PURE_REVERT_BAD_ARGUMENT");
    }

    [Fact]
    public void ExtraArgumentsAreRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();

        AssertRejected(
            Run([fixture.Repository, fixture.RootSha, "unexpected"]),
            "PURE_REVERT_BAD_ARGUMENT");
    }

    [Fact]
    public void ReversedRepositoryAndHintArgumentsAreRejected()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();

        AssertRejected(
            Run([fixture.RootSha, fixture.Repository]),
            "PURE_REVERT_BAD_ARGUMENT");
    }

    [Fact]
    public void GitCommandFailureFailsClosedWithNamedReason()
    {
        if (OperatingSystem.IsWindows()) return;
        using var fixture = new GitFixture();
        fixture.CommitFiles("seed", new FileMutation("tools/target.txt", "before\n"));
        fixture.CommitFiles("target", new FileMutation("tools/target.txt", "after\n"));
        fixture.CommitCandidateAndMerge(
            "inverse",
            new FileMutation("tools/target.txt", "before\n"));
        var failingGitPath = fixture.CreateFailingGitPath("diff-tree");

        AssertRejected(
            Run([fixture.Repository], failingGitPath),
            "PURE_REVERT_GIT_FAILURE");
    }

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
        var command = executablePath is null ? "/bin/bash" : "/usr/bin/env";
        var commandArguments = executablePath is null
            ? new[] { script }.Concat(arguments).ToArray()
            : new[]
                {
                    $"PATH={executablePath}:/usr/bin:/bin:/usr/sbin:/sbin",
                    "/bin/bash",
                    script,
                }
                .Concat(arguments)
                .ToArray();
        return TestProcessRunner.Run(
            command,
            commandArguments,
            root,
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
        private static readonly string ProtectionPolicy = """
            internal static class BootstrapProtectionPolicy
            {
                internal static object Matchers => new[]
                {
                    Atom("tools", ProtectionMatchKind.Prefix, "tools/"),
                    Atom("workflows", ProtectionMatchKind.Prefix, "{workflow-prefix}"),
                };
            }
            """.Replace(
                "{workflow-prefix}",
                ".github/" + "work" + "flows/",
                StringComparison.Ordinal);

        private readonly TemporaryDirectory temporary = new();

        internal GitFixture()
        {
            Repository = Path.Combine(temporary.Path, "repository");
            ScriptHarnessScratch.EnsureDirectory(Repository);
            Git("init", "-b", "main");
            Git("config", "user.name", "Pure Revert Test");
            Git("config", "user.email", "pure-revert@example.invalid");
            CommitFiles(
                "canonical policy",
                new FileMutation(
                    "tools/StrataLint.Engine/Admission/BootstrapProtectionPolicy.cs",
                    ProtectionPolicy));
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
                "/usr/bin/git",
                ["clone", "--depth=1", new Uri(Repository).AbsoluteUri, shallow],
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
                "/usr/bin/git",
                arguments,
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
        }

        private string GitText(params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/git",
                arguments,
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024);
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        private string GitTextWithInput(string input, params string[] arguments)
        {
            var result = TestProcessRunner.Run(
                "/usr/bin/git",
                arguments,
                Repository,
                TestBudgets.ScriptProcessHangGuard,
                64 * 1024,
                Encoding.UTF8.GetBytes(input));
            Assert.True(result.ExitCode == 0, Diagnostics(result));
            return Encoding.UTF8.GetString(result.StandardOutput).Trim();
        }

        public void Dispose() => temporary.Dispose();
    }

    private static string Diagnostics(ProcessOutput result) =>
        "stdout:\n" + Encoding.UTF8.GetString(result.StandardOutput)
        + "\nstderr:\n" + Encoding.UTF8.GetString(result.StandardError);
}
