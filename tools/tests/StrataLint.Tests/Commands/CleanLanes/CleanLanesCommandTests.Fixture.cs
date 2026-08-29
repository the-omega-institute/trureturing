using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    private sealed partial class CleanLanesFixture
    {
        internal enum OwnedDirectory
        {
            Temporary,
            Worktrees,
            Repository,
        }

        private readonly TemporaryDirectory repository;
        private readonly TemporaryDirectory worktrees;
        private readonly TemporaryDirectory temp;
        private Action disposeRepository;
        private Action disposeWorktrees;
        private Action disposeTemp;
        private readonly Dictionary<string, PullRequestProbeOutcome> pullRequests =
            new(StringComparer.Ordinal);
        private readonly Dictionary<string, LaneProcessProbeOutcome> laneProcesses =
            new(StringComparer.Ordinal);
        private DateTimeOffset now;

        internal CleanLanesFixture(TestScratchRoot? scratchRoot = null)
        {
            var root = scratchRoot ?? TestScratchRoot.Current;
            repository = new TemporaryDirectory(root);
            worktrees = new TemporaryDirectory(root);
            temp = new TemporaryDirectory(root);
            disposeRepository = repository.Dispose;
            disposeWorktrees = worktrees.Dispose;
            disposeTemp = temp.Dispose;
            Git(repository.Path, "init", "--initial-branch=dev");
            Git(repository.Path, "config", "user.email", "stratalint@example.invalid");
            Git(repository.Path, "config", "user.name", "StrataLint Tests");
            File.WriteAllText(
                Path.Combine(repository.Path, "README.md"),
                "# clean lanes fixture\n",
                new UTF8Encoding(false));
            Git(repository.Path, "add", "README.md");
            Git(repository.Path, "commit", "-m", "fixture baseline");
            now = new DateTimeOffset(2030, 1, 2, 0, 0, 0, TestBudgets.ZeroDuration);
        }

        internal string RepositoryRoot =>
            Git(repository.Path, "rev-parse", "--show-toplevel").Trim();

        internal string RepositoryWorkingDirectory => repository.Path;

        internal string[] OwnedWorkingDirectories => [temp.Path, worktrees.Path, repository.Path];

        internal string OwnedWorkingDirectory(OwnedDirectory directory) => directory switch
        {
            OwnedDirectory.Temporary => temp.Path,
            OwnedDirectory.Worktrees => worktrees.Path,
            OwnedDirectory.Repository => repository.Path,
            _ => throw new ArgumentOutOfRangeException(nameof(directory), directory, null),
        };

        internal void SetOwnedDirectoryDisposer(OwnedDirectory directory, Action disposer)
        {
            ArgumentNullException.ThrowIfNull(disposer);
            switch (directory)
            {
                case OwnedDirectory.Temporary:
                    disposeTemp = disposer;
                    break;
                case OwnedDirectory.Worktrees:
                    disposeWorktrees = disposer;
                    break;
                case OwnedDirectory.Repository:
                    disposeRepository = disposer;
                    break;
                default:
                    throw new ArgumentOutOfRangeException(nameof(directory), directory, null);
            }
        }

        internal void RestoreOwnedDirectoryDisposer(OwnedDirectory directory) =>
            SetOwnedDirectoryDisposer(
                directory,
                directory switch
                {
                    OwnedDirectory.Temporary => temp.Dispose,
                    OwnedDirectory.Worktrees => worktrees.Dispose,
                    OwnedDirectory.Repository => repository.Dispose,
                    _ => throw new ArgumentOutOfRangeException(nameof(directory), directory, null),
                });

        internal string Head(string path) => Git(path, "rev-parse", "HEAD").Trim();

        internal bool WorktreeRegistered(string path) =>
            Git(repository.Path, "worktree", "list", "--porcelain")
                .Split('\n', StringSplitOptions.RemoveEmptyEntries)
                .Contains($"worktree {path}", StringComparer.Ordinal);

        internal DateTimeOffset CreationTime(string path)
        {
            var firstLine = File.ReadLines(CreationLogPath(path), Encoding.UTF8).First();
            var left = firstLine.Split('\t', 2)[0];
            var fields = left.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            return DateTimeOffset.FromUnixTimeSeconds(long.Parse(
                fields[^2],
                System.Globalization.CultureInfo.InvariantCulture));
        }

        internal void DeleteCreationLog(string path) => File.Delete(CreationLogPath(path));

        internal void EmptyCreationLog(string path) =>
            File.WriteAllText(CreationLogPath(path), string.Empty, new UTF8Encoding(false));

        /// <summary>
        /// 把首条 reflog 记录的 message 清空,即让行**以制表符结尾** ——
        /// 这是本机 89.8% 的 worktree 的真实形状(#3459),不是畸形。
        /// </summary>
        internal void MakeFirstRecordEmptyMessage(string path)
        {
            var logPath = CreationLogPath(path);
            var lines = File.ReadAllLines(logPath, Encoding.UTF8);
            var tab = lines[0].IndexOf('\t');
            lines[0] = (tab < 0 ? lines[0] : lines[0][..tab]) + "\t";
            File.WriteAllText(
                logPath,
                string.Join('\n', lines) + "\n",
                new UTF8Encoding(false));
        }

        /// <summary>把首条 reflog 记录写成**没有制表符**的形状(本机 11 棵新树即此形)。</summary>
        internal void MakeFirstRecordWithoutTab(string path)
        {
            var logPath = CreationLogPath(path);
            var lines = File.ReadAllLines(logPath, Encoding.UTF8);
            var tab = lines[0].IndexOf('\t');
            lines[0] = tab < 0 ? lines[0] : lines[0][..tab];
            File.WriteAllText(
                logPath,
                string.Join('\n', lines) + "\n",
                new UTF8Encoding(false));
        }

        internal void MakeFirstRecordNonCreation(string path)
        {
            var logPath = CreationLogPath(path);
            var text = File.ReadAllText(logPath, Encoding.UTF8);
            var firstSpace = text.IndexOf(' ');
            File.WriteAllText(
                logPath,
                Head(path) + text[firstSpace..],
                new UTF8Encoding(false));
        }

        internal void LockLane(string path) =>
            Git(repository.Path, "worktree", "lock", "--reason", "fixture session", path);

        internal void RegisterMergedPr(string branch, string headOid, string mergeCommitOid) =>
            pullRequests[branch] = new PullRequestProbeOutcome(
                true,
                [new PullRequestInfo(branch, headOid, "MERGED", mergeCommitOid)]);

        internal void RegisterPullRequests(
            string lookupBranch,
            params PullRequestInfo[] returnedPullRequests) =>
            pullRequests[lookupBranch] = new PullRequestProbeOutcome(
                true,
                returnedPullRequests);

        internal void RegisterClosedPr(string branch, string headOid) =>
            pullRequests[branch] = new PullRequestProbeOutcome(
                true,
                [new PullRequestInfo(branch, headOid, "CLOSED", null)]);

        internal void FailPrProbe(string branch) =>
            pullRequests[branch] = new PullRequestProbeOutcome(false, []);

        internal void MarkLaneInUse(string path) =>
            laneProcesses[path] = new LaneProcessProbeOutcome(true, true);

        internal void FailProcessProbe(string path) =>
            laneProcesses[path] = new LaneProcessProbeOutcome(false, false);

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

        internal string AddMergedLane(string branch, bool dirty = false)
        {
            var path = WorktreePath(branch);
            AddWorktree(branch, path);
            var canonicalPath = Git(path, "rev-parse", "--show-toplevel").Trim();
            RegisterMergedPr(branch, Head(canonicalPath), Head(canonicalPath));
            if (dirty)
            {
                File.WriteAllText(
                    Path.Combine(canonicalPath, "dirty.txt"),
                    "untracked\n",
                    new UTF8Encoding(false));
            }

            return canonicalPath;
        }

        internal string AddLandedLane(string branch, bool dirty = false)
        {
            var path = AddMergedLane(branch);
            var artifact = branch.Replace('/', '-') + ".txt";
            File.WriteAllText(
                Path.Combine(path, artifact),
                "landed lane work\n",
                new UTF8Encoding(false));
            Git(path, "add", artifact);
            Git(path, "commit", "-m", $"land {branch}");
            Git(repository.Path, "merge", "--ff-only", branch);
            var head = Head(path);
            RegisterMergedPr(branch, head, head);
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

        internal CommandResult Run(params string[] arguments) =>
            RunCore(
                CreateRunner(),
                now,
                ProbePullRequests,
                ProbeLaneProcesses,
                arguments);

        internal CommandResult RunAt(DateTimeOffset injectedNow, params string[] arguments) =>
            RunCore(
                CreateRunner(),
                injectedNow,
                ProbePullRequests,
                ProbeLaneProcesses,
                arguments);

        internal CommandResult RunWithBase(string baseRevision, params string[] arguments) =>
            RunCore(
                CreateRunner(),
                now,
                ProbePullRequests,
                ProbeLaneProcesses,
                arguments,
                baseRevision);

        internal CommandResult RunWithProbes(
            PullRequestProbe pullRequestProbe,
            LaneProcessProbe laneProcessProbe,
            params string[] arguments) =>
            RunCore(
                CreateRunner(),
                now,
                pullRequestProbe,
                laneProcessProbe,
                arguments);

        internal CommandResult RunWithLaneProcessProbe(
            LaneProcessProbe laneProcessProbe,
            params string[] arguments) =>
            RunCore(
                CreateRunner(),
                now,
                ProbePullRequests,
                laneProcessProbe,
                arguments);

        internal CommandResult RunWith(
            IWorktreeProcessRunner runner,
            params string[] arguments) =>
            RunCore(CreateRunner(runner), now, ProbePullRequests, ProbeLaneProcesses, arguments);

        internal ScriptedWorktreeProcessRunner CreateRunner(ProcessScript? script = null) =>
            CreateRunner(new ProductionWorktreeProcessRunner(), script);

        internal CommandResult RunWithRaw(
            IWorktreeProcessRunner runner,
            params string[] arguments) =>
            RunCore(runner, now, ProbePullRequests, ProbeLaneProcesses, arguments);

        internal CommandResult RunWithProductionProbes(
            IWorktreeProcessRunner runner,
            params string[] arguments)
        {
            var allArguments = new List<string> { "--base", "dev" };
            allArguments.AddRange(arguments);
            return CleanLanesCommand.Run(
                repository.Path,
                allArguments,
                runner,
                [temp.Path],
                now);
        }

        private ScriptedWorktreeProcessRunner CreateRunner(
            IWorktreeProcessRunner inner,
            ProcessScript? script = null) =>
            new(
                inner,
                script ?? (static (_, _, _) => null));

        private CommandResult RunCore(
            IWorktreeProcessRunner runner,
            DateTimeOffset injectedNow,
            PullRequestProbe pullRequestProbe,
            LaneProcessProbe laneProcessProbe,
            IReadOnlyList<string> arguments,
            string baseRevision = "dev")
        {
            var allArguments = new List<string> { "--base", baseRevision };
            allArguments.AddRange(arguments);
            return CleanLanesCommand.Run(
                repository.Path,
                allArguments,
                runner,
                [temp.Path],
                injectedNow,
                pullRequestProbe,
                laneProcessProbe);
        }
    }
}

internal delegate ProcessOutput? ProcessScript(
    string fileName,
    IReadOnlyList<string> arguments,
    string workingDirectory);

internal sealed class ScriptedWorktreeProcessRunner(
    IWorktreeProcessRunner inner,
    ProcessScript script) : IWorktreeProcessRunner
{
    internal List<WorktreeProcessInvocation> Invocations { get; } = [];

    public ProcessOutput Run(
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout)
    {
        Invocations.Add(new WorktreeProcessInvocation(
            fileName,
            arguments.ToArray(),
            workingDirectory,
            timeout));
        return script(fileName, arguments, workingDirectory)
            ?? inner.Run(fileName, arguments, workingDirectory, timeout);
    }
}
