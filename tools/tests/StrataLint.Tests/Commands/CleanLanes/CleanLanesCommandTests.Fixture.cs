using System.Runtime.ExceptionServices;
using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    private sealed partial class CleanLanesFixture
    {
        internal enum RepositoryDirectoryState
        {
            Absent,
            Present,
            Indeterminate,
        }

        internal readonly record struct RepositoryDirectoryProbe(
            RepositoryDirectoryState State,
            ExceptionDispatchInfo? Failure = null);

        private readonly TemporaryDirectory repository;
        private readonly TemporaryDirectory worktrees;
        private readonly TemporaryDirectory temp;
        private readonly Dictionary<string, PullRequestProbeOutcome> pullRequests =
            new(StringComparer.Ordinal);
        private readonly Dictionary<string, LaneProcessProbeOutcome> laneProcesses =
            new(StringComparer.Ordinal);
        private Func<string, FileAttributes> repositoryAttributesReader = File.GetAttributes;
        private DateTimeOffset now;

        internal CleanLanesFixture(TestScratchRoot? scratchRoot = null)
        {
            var root = scratchRoot ?? TestScratchRoot.Current;
            repository = new TemporaryDirectory(root);
            worktrees = new TemporaryDirectory(root);
            temp = new TemporaryDirectory(root);
            Git(repository.Path, "init", "--initial-branch=dev");
            Git(repository.Path, "config", "user.email", "stratalint@example.invalid");
            Git(repository.Path, "config", "user.name", "StrataLint Tests");
            File.WriteAllText(
                Path.Combine(repository.Path, "README.md"),
                "# clean lanes fixture\n",
                new UTF8Encoding(false));
            Git(repository.Path, "add", "README.md");
            Git(repository.Path, "commit", "-m", "fixture baseline");
            now = TimeProvider.System.GetUtcNow().AddHours(48);
        }

        internal string RepositoryRoot =>
            Git(repository.Path, "rev-parse", "--show-toplevel").Trim();

        internal string RepositoryWorkingDirectory => repository.Path;

        internal string[] OwnedWorkingDirectories => [temp.Path, worktrees.Path, repository.Path];

        internal void SetRepositoryAttributesReader(Func<string, FileAttributes> reader) =>
            repositoryAttributesReader = reader;

        internal void RestoreRepositoryAttributesReader() =>
            repositoryAttributesReader = File.GetAttributes;

        internal RepositoryDirectoryProbe ProbeRepositoryDirectory()
        {
            try
            {
                var attributes = repositoryAttributesReader(repository.Path);
                return (attributes & FileAttributes.Directory) != 0
                    ? new RepositoryDirectoryProbe(RepositoryDirectoryState.Present)
                    : new RepositoryDirectoryProbe(
                        RepositoryDirectoryState.Indeterminate,
                        ExceptionDispatchInfo.Capture(new IOException(
                            $"owned repository path is not a directory: {repository.Path}")));
            }
            catch (FileNotFoundException)
            {
                return new RepositoryDirectoryProbe(RepositoryDirectoryState.Absent);
            }
            catch (Exception exception) when (exception is UnauthorizedAccessException or IOException)
            {
                return new RepositoryDirectoryProbe(
                    RepositoryDirectoryState.Indeterminate,
                    ExceptionDispatchInfo.Capture(exception));
            }
        }

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
