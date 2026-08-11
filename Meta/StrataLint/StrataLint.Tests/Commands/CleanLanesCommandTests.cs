using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

[Trait("Category", "Script")] public sealed class CleanLanesCommandTests
{
    [Fact]
    public void RootUsageListsCleanLanesCommand()
    {
        var console = new BufferedConsole();

        var exitCode = CliApplication.Run(
            [],
            new StubCliEnvironment(new AdmissionOutcome.InfrastructureFailure("unused")),
            console);

        Assert.Equal(2, exitCode);
        Assert.Contains("clean-lanes", console.Error, StringComparison.Ordinal);
    }

    [Fact]
    public void ParseUsesDryRunAndDevBaseByDefault()
    {
        var options = CleanLanesCommand.ParseArguments([]);

        Assert.Equal("origin/dev", options.Base);
        Assert.False(options.Force);
    }

    [Theory]
    [InlineData("--unknown")]
    [InlineData("--base")]
    [InlineData("--force", "--force")]
    public void ParseRejectsUnknownMissingOrDuplicateArguments(params string[] arguments)
    {
        var exception = Assert.Throws<InvalidOperationException>(() =>
            CleanLanesCommand.ParseArguments(arguments));

        Assert.Contains("USAGE: StrataLint clean-lanes", exception.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DryRunListsEligibleItemsWithoutMutation()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/merged");
        fixture.AddOrphan("harness/orphan", merged: true);
        var judge = fixture.AddDetachedJudge("trureturing-gate-judge");

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.True(Directory.Exists(judge));
        Assert.True(fixture.BranchExists("harness/merged"));
        Assert.True(fixture.BranchExists("harness/orphan"));
        Assert.Contains("\"kind\":\"merged_worktree\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"kind\":\"orphan_branch\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"kind\":\"temp_judge\"", result.Output, StringComparison.Ordinal);
        Assert.Equal(3, Count(result.Output, "\"action\":\"would_remove\""));
    }

    [Fact]
    public void ForceRemovesEligibleItemsAndProtectsEveryIneligibleClass()
    {
        using var fixture = new CleanLanesFixture();
        var removable = fixture.AddMergedLane("harness/merged");
        var dirty = fixture.AddMergedLane("harness/dirty", dirty: true);
        var unmerged = fixture.AddUnmergedLane("harness/unmerged");
        fixture.AddOrphan("harness/orphan", merged: true);
        fixture.AddOrphan("harness/orphan-unmerged", merged: false);
        fixture.AddOrphan("agent/prover/not-an-init-branch", merged: true);
        var foreign = fixture.AddForeignTempDirectory("trureturing-foreign");
        var attached = fixture.AddAttachedTempDirectory("trureturing-attached");

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(removable));
        Assert.False(fixture.BranchExists("harness/merged"));
        Assert.False(fixture.BranchExists("harness/orphan"));
        Assert.True(Directory.Exists(dirty));
        Assert.True(Directory.Exists(unmerged));
        Assert.True(Directory.Exists(foreign));
        Assert.True(Directory.Exists(attached));
        Assert.True(fixture.BranchExists("harness/dirty"));
        Assert.True(fixture.BranchExists("harness/unmerged"));
        Assert.True(fixture.BranchExists("harness/orphan-unmerged"));
        Assert.True(fixture.BranchExists("agent/prover/not-an-init-branch"));
        Assert.Contains("\"reason\":\"dirty\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"reason\":\"unmerged\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"reason\":\"foreign_git_directory\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"reason\":\"attached_branch\"", result.Output, StringComparison.Ordinal);
        Assert.DoesNotContain(
            $"\"path\":\"{Escape(fixture.RepositoryRoot)}\",\"action\":\"removed\"",
            result.Output,
            StringComparison.Ordinal);
    }

    [Fact]
    public void ForceRemovesDetachedJudgeFromTheSameRepository()
    {
        using var fixture = new CleanLanesFixture();
        var judge = fixture.AddDetachedJudge("trureturing-detached");

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(judge));
        Assert.Contains("\"kind\":\"temp_judge\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"action\":\"removed\"", result.Output, StringComparison.Ordinal);
    }

    [Fact]
    public void ForceRemovesGitlessJudgeSnapshotButKeepsReportDirectory()
    {
        using var fixture = new CleanLanesFixture();
        var judge = fixture.AddGitlessJudgeSnapshot("trureturing-snapshot-judge");
        var reports = fixture.AddReportDirectory("trureturing-report-files");

        var result = fixture.Run("--force");

        Assert.True(result.Success, result.Error);
        Assert.False(Directory.Exists(judge));
        Assert.True(Directory.Exists(reports));
        Assert.Contains("\"reason\":\"gitless_judge_snapshot\"", result.Output, StringComparison.Ordinal);
        Assert.Contains("\"reason\":\"not_judge_tree\"", result.Output, StringComparison.Ordinal);
    }

    private static int Count(string value, string needle) =>
        value.Split(needle, StringSplitOptions.None).Length - 1;

    private static string Escape(string value) => value.Replace("\\", "\\\\", StringComparison.Ordinal);

    private sealed class CleanLanesFixture : IDisposable
    {
        private readonly TemporaryDirectory repository = new();
        private readonly TemporaryDirectory worktrees = new();
        private readonly TemporaryDirectory temp = new();

        internal CleanLanesFixture()
        {
            Git(repository.Path, "init", "--initial-branch=dev");
            Git(repository.Path, "config", "user.email", "stratalint@example.invalid");
            Git(repository.Path, "config", "user.name", "StrataLint Tests");
            File.WriteAllText(
                Path.Combine(repository.Path, "README.md"),
                "# clean lanes fixture\n",
                new UTF8Encoding(false));
            Git(repository.Path, "add", "README.md");
            Git(repository.Path, "commit", "-m", "fixture baseline");
        }

        internal string RepositoryRoot => repository.Path;

        internal string AddMergedLane(string branch, bool dirty = false)
        {
            var path = WorktreePath(branch);
            Git(repository.Path, "worktree", "add", "-b", branch, path, "dev");
            if (dirty)
            {
                File.WriteAllText(
                    Path.Combine(path, "dirty.txt"),
                    "untracked\n",
                    new UTF8Encoding(false));
            }

            return path;
        }

        internal string AddUnmergedLane(string branch)
        {
            var path = AddMergedLane(branch);
            File.WriteAllText(
                Path.Combine(path, "unmerged.txt"),
                "branch-only\n",
                new UTF8Encoding(false));
            Git(path, "add", "unmerged.txt");
            Git(path, "commit", "-m", "unmerged branch commit");
            return path;
        }

        internal void AddOrphan(string branch, bool merged)
        {
            if (merged)
            {
                Git(repository.Path, "branch", branch, "dev");
                return;
            }

            var path = AddUnmergedLane(branch);
            Git(repository.Path, "worktree", "remove", path);
        }

        internal string AddDetachedJudge(string name)
        {
            var path = Path.Combine(temp.Path, name);
            Git(repository.Path, "worktree", "add", "--detach", path, "dev");
            return path;
        }

        internal string AddForeignTempDirectory(string name)
        {
            var path = Path.Combine(temp.Path, name);
            Directory.CreateDirectory(path);
            Git(path, "init", "--initial-branch=dev");
            return path;
        }

        internal string AddAttachedTempDirectory(string name)
        {
            var path = Path.Combine(temp.Path, name);
            Git(repository.Path, "worktree", "add", "-b", "scratch/attached", path, "dev");
            return path;
        }

        internal string AddGitlessJudgeSnapshot(string name)
        {
            var path = Path.Combine(temp.Path, name);
            Directory.CreateDirectory(Path.Combine(path, "D5"));
            Directory.CreateDirectory(Path.Combine(path, "Meta", "StrataLint"));
            Directory.CreateDirectory(Path.Combine(path, ".github", "scripts"));
            File.WriteAllText(Path.Combine(path, "CLAUDE.md"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(path, "AGENTS.md"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(path, "Trureturing.lean"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(path, "lean-toolchain"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(path, ".github", "scripts", "harness-gate.sh"),
                "fixture\n",
                new UTF8Encoding(false));
            return path;
        }

        internal string AddReportDirectory(string name)
        {
            var path = Path.Combine(temp.Path, name);
            Directory.CreateDirectory(path);
            File.WriteAllText(Path.Combine(path, "candidate.json"), "{}\n", new UTF8Encoding(false));
            return path;
        }

        internal CommandResult Run(params string[] arguments)
        {
            var allArguments = new List<string> { "--base", "dev" };
            allArguments.AddRange(arguments);
            return CleanLanesCommand.Run(
                repository.Path,
                allArguments,
                new ProductionWorktreeProcessRunner(),
                [temp.Path]);
        }

        internal bool BranchExists(string branch)
        {
            var result = BoundedProcessRunner.Run(
                "git",
                ["show-ref", "--verify", "--quiet", $"refs/heads/{branch}"],
                repository.Path,
                TimeSpan.FromSeconds(30),
                4096);
            return result.ExitCode == 0;
        }

        public void Dispose()
        {
            var inventory = BoundedProcessRunner.Run(
                "git",
                ["worktree", "list", "--porcelain"],
                repository.Path,
                TimeSpan.FromSeconds(30),
                1024 * 1024);
            if (inventory.ExitCode == 0)
            {
                var root = Path.GetFullPath(repository.Path);
                var paths = Encoding.UTF8.GetString(inventory.StandardOutput)
                    .Split('\n', StringSplitOptions.RemoveEmptyEntries)
                    .Where(static line => line.StartsWith("worktree ", StringComparison.Ordinal))
                    .Select(static line => line["worktree ".Length..])
                    .Where(path => !string.Equals(Path.GetFullPath(path), root, StringComparison.Ordinal))
                    .ToArray();
                foreach (var path in paths)
                {
                    BoundedProcessRunner.Run(
                        "git",
                        ["worktree", "remove", "--force", path],
                        repository.Path,
                        TimeSpan.FromSeconds(30),
                        1024 * 1024);
                }
            }

            temp.Dispose();
            worktrees.Dispose();
            repository.Dispose();
        }

        private string WorktreePath(string branch) =>
            Path.Combine(worktrees.Path, branch.Replace('/', '-'));

        private static string Git(string root, params string[] arguments) =>
            ReviewRegressionTests.RunGit(root, arguments);
    }
}
