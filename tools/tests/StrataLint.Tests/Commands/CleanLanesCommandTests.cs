using System.Text;
using System.Text.Json;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class CleanLanesCommandTests
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
    public void UnreadableRegisteredLaneIsSkippedWithoutHidingHealthyLanes()
    {
        using var fixture = new CleanLanesFixture();
        var unreadable = fixture.AddMergedLane("harness/unreadable");
        var healthy = fixture.AddMergedLane("harness/healthy");
        File.Delete(Path.Combine(unreadable, ".git"));

        Assert.True(Directory.Exists(unreadable));
        Assert.False(File.Exists(Path.Combine(unreadable, ".git")));

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        var items = ReadItems(result.Output);
        Assert.Contains(items, item =>
            ItemMatches(item, unreadable, "skipped", "unreadable"));
        Assert.Contains(items, item =>
            ItemMatches(item, healthy, "would_remove", "merged_clean"));
    }

    [Fact]
    public void AncestryInspectionFailureSkipsOnlyAffectedLane()
    {
        using var fixture = new CleanLanesFixture();
        var unreadable = fixture.AddMergedLane("harness/ancestry-unreadable");
        var unreadableHead = fixture.Head(unreadable);
        fixture.AdvanceDev();
        var healthy = fixture.AddMergedLane("harness/ancestry-healthy");
        var runner = new SelectiveFailureRunner(
            arguments => arguments.Count > 2
                && arguments[0] == "merge-base"
                && arguments[2] == unreadableHead,
            "synthetic ancestry inspection failure");

        var result = fixture.RunWith(runner);

        Assert.True(result.Success, result.Error);
        var items = ReadItems(result.Output);
        Assert.Contains(items, item =>
            ItemMatches(item, unreadable, "skipped", "unreadable"));
        Assert.Contains(items, item =>
            ItemMatches(item, healthy, "would_remove", "merged_clean"));
    }

    [Fact]
    public void BaseResolutionFailureRemainsFailClosed()
    {
        using var fixture = new CleanLanesFixture();
        var runner = new SelectiveFailureRunner(
            arguments => arguments.Count > 0
                && arguments[0] == "rev-parse"
                && arguments[^1] == "dev^{commit}",
            "synthetic base resolution failure");

        var result = fixture.RunWith(runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal("CLEAN_LANES_FAILED synthetic base resolution failure\n", result.Error);
    }

    [Fact]
    public void WorktreeEnumerationFailureRemainsFailClosed()
    {
        using var fixture = new CleanLanesFixture();
        var runner = new SelectiveFailureRunner(
            arguments => arguments.Count > 1
                && arguments[0] == "worktree"
                && arguments[1] == "list",
            "synthetic worktree enumeration failure");

        var result = fixture.RunWith(runner);

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal("CLEAN_LANES_FAILED synthetic worktree enumeration failure\n", result.Error);
    }

    [Fact]
    public void BlockedWorktreesRetainEstablishedReasons()
    {
        using var fixture = new CleanLanesFixture();
        fixture.SwitchToManagedBranch("harness/current");
        var missing = fixture.AddMergedLane("harness/missing");
        var dirty = fixture.AddMergedLane("harness/dirty", dirty: true);
        var unmerged = fixture.AddUnmergedLane("harness/unmerged");
        Directory.Delete(missing, recursive: true);

        var result = fixture.Run();

        Assert.True(result.Success, result.Error);
        var items = ReadItems(result.Output);
        Assert.Contains(items, item =>
            ItemMatches(item, fixture.RepositoryRoot, "skipped", "current"));
        Assert.Contains(items, item =>
            ItemMatches(item, missing, "skipped", "missing"));
        Assert.Contains(items, item =>
            ItemMatches(item, dirty, "skipped", "dirty"));
        Assert.Contains(items, item =>
            ItemMatches(item, unmerged, "skipped", "unmerged"));
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

    [Fact]
    public void ForceRemovalFailureRemainsFailClosed()
    {
        using var fixture = new CleanLanesFixture();
        var lane = fixture.AddMergedLane("harness/remove-failure");
        var runner = new SelectiveFailureRunner(
            arguments => arguments.Count > 1
                && arguments[0] == "worktree"
                && arguments[1] == "remove",
            "synthetic worktree removal failure");

        var result = fixture.RunWith(runner, "--force");

        Assert.False(result.Success);
        Assert.Empty(result.Output);
        Assert.Equal("CLEAN_LANES_FAILED synthetic worktree removal failure\n", result.Error);
        Assert.True(Directory.Exists(lane));
        Assert.True(fixture.BranchExists("harness/remove-failure"));
    }

    private static int Count(string value, string needle) =>
        value.Split(needle, StringSplitOptions.None).Length - 1;

    private static IReadOnlyList<JsonElement> ReadItems(string output)
    {
        var items = new List<JsonElement>();
        foreach (var line in output.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            using var document = JsonDocument.Parse(line);
            if (document.RootElement.GetProperty("event").GetString() == "clean_lanes_item")
            {
                items.Add(document.RootElement.Clone());
            }
        }

        return items;
    }

    private static bool ItemMatches(
        JsonElement item,
        string path,
        string action,
        string reason) =>
        item.GetProperty("path").GetString() == path
        && item.GetProperty("action").GetString() == action
        && item.GetProperty("reason").GetString() == reason;

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

        internal string RepositoryRoot =>
            Git(repository.Path, "rev-parse", "--show-toplevel").Trim();

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

            return Git(path, "rev-parse", "--show-toplevel").Trim();
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

        internal void AdvanceDev()
        {
            File.AppendAllText(
                Path.Combine(repository.Path, "README.md"),
                "advance\n",
                new UTF8Encoding(false));
            Git(repository.Path, "add", "README.md");
            Git(repository.Path, "commit", "-m", "advance dev");
        }

        internal string Head(string path) => Git(path, "rev-parse", "HEAD").Trim();

        internal void SwitchToManagedBranch(string branch) =>
            Git(repository.Path, "switch", "-c", branch);

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
            Directory.CreateDirectory(Path.Combine(path, "tools"));
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
            => RunWith(new ProductionWorktreeProcessRunner(), arguments);

        internal CommandResult RunWith(
            IWorktreeProcessRunner runner,
            params string[] arguments)
        {
            var allArguments = new List<string> { "--base", "dev" };
            allArguments.AddRange(arguments);
            return CleanLanesCommand.Run(
                repository.Path,
                allArguments,
                runner,
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

    private sealed class SelectiveFailureRunner(
        Func<IReadOnlyList<string>, bool> shouldFail,
        string error) : IWorktreeProcessRunner
    {
        private readonly ProductionWorktreeProcessRunner inner = new();

        public ProcessOutput Run(
            string fileName,
            IReadOnlyList<string> arguments,
            string workingDirectory,
            TimeSpan timeout) =>
            fileName == "git" && shouldFail(arguments)
                ? new ProcessOutput(128, [], Encoding.UTF8.GetBytes(error + "\n"))
                : inner.Run(fileName, arguments, workingDirectory, timeout);
    }
}
