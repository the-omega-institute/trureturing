using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class CleanLanesCommandTests
{
    private sealed partial class CleanLanesFixture
    {
        private static readonly string TemplateRepositoryPath = CreateTemplateRepository();

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
            CopyDirectory(TemplateRepositoryPath, repository.Path);
            now = new DateTimeOffset(2030, 1, 2, 0, 0, 0, TestBudgets.ZeroDuration);
        }

        private static string CreateTemplateRepository()
        {
            var path = TestScratchRoot.Current.CreateDirectory();
            Git(path, "init", "--initial-branch=dev");
            Git(path, "config", "user.email", "stratalint@example.invalid");
            Git(path, "config", "user.name", "StrataLint Tests");
            File.WriteAllText(
                Path.Combine(path, "README.md"),
                "# clean lanes fixture\n",
                new UTF8Encoding(false));
            Git(path, "add", "README.md");
            // The template is copied immediately; maintenance must not keep modifying .git.
            Git(path, "-c", "maintenance.auto=false", "commit", "-m", "fixture baseline");
            return path;
        }

        private static void CopyDirectory(string sourcePath, string targetPath)
        {
            foreach (var directory in Directory.EnumerateDirectories(
                         sourcePath,
                         "*",
                         SearchOption.AllDirectories))
            {
                Directory.CreateDirectory(Path.Combine(
                    targetPath,
                    Path.GetRelativePath(sourcePath, directory)));
            }

            foreach (var file in StrataLint.TestSupport.TemporaryFileSystem.Directory.EnumerateFiles(
                         sourcePath,
                         "*",
                         SearchOption.AllDirectories))
            {
                File.Copy(
                    file,
                    Path.Combine(targetPath, Path.GetRelativePath(sourcePath, file)));
            }
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

        internal static void AssertDirectoryExists(string path, bool expected) =>
            Assert.Equal(expected, Directory.Exists(path));

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
            return Git(path, "rev-parse", "--show-toplevel").Trim();
        }

        internal string AddNestedWorktree(string parent)
        {
            var path = Path.Combine(parent, "nested");
            Git(repository.Path, "worktree", "add", "--detach", path, "dev");
            return Git(path, "rev-parse", "--show-toplevel").Trim();
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
            Directory.CreateDirectory(Path.Combine(path, "tools", "scripts"));
            File.WriteAllText(Path.Combine(path, "CLAUDE.md"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(path, "AGENTS.md"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(path, "Trureturing.lean"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(path, "lean-toolchain"), "fixture\n", new UTF8Encoding(false));
            File.WriteAllText(
                Path.Combine(path, "tools", "scripts", "ci-stage.sh"),
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
            AdvanceBase(300);
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
            AdvanceBase(300);
            return path;
        }

        internal CommandResult Run(params string[] arguments) =>
            RunCore(CreateRunner(), now, arguments);

        internal CommandResult RunAt(DateTimeOffset injectedNow, params string[] arguments) =>
            RunCore(CreateRunner(), injectedNow, arguments);

        internal CommandResult RunWithBase(string baseRevision, params string[] arguments) =>
            RunCore(CreateRunner(), now, arguments, baseRevision);

        internal CommandResult RunWith(IWorktreeProcessRunner runner, params string[] arguments) =>
            RunCore(CreateRunner(runner), now, arguments);

        internal void AdvanceBase(int count)
        {
            var stream = new StringBuilder();
            for (var index = 0; index < count; index++)
            {
                stream.Append("commit refs/heads/dev\ncommitter Test <test@example.invalid> 1700000000 +0000\ndata 1\nx\n");
                if (index == 0) stream.Append($"from {Head(repository.Path)}\n");
                stream.Append('\n');
            }

            var result = TestProcessRunner.Run("git", ["fast-import", "--quiet", "--force"],
                repository.Path, BoundedProcessRunner.HangDetectionBudget, 4096,
                Encoding.UTF8.GetBytes(stream.ToString()));
            Assert.Equal(0, result.ExitCode);
        }

        internal DateTimeOffset LastUpdate(string path) => DateTimeOffset.FromUnixTimeSeconds(
            File.ReadLines(CreationLogPath(path)).Select(line => long.Parse(
                line.Split('\t')[0].Split(' ', StringSplitOptions.RemoveEmptyEntries)[^2],
                System.Globalization.CultureInfo.InvariantCulture)).Max());

        internal void RewriteLastUpdate(string path, DateTimeOffset time)
        {
            var log = CreationLogPath(path);
            var lines = File.ReadAllLines(log);
            var tab = lines[^1].IndexOf('\t');
            var fields = (tab < 0 ? lines[^1] : lines[^1][..tab]).Split(' ');
            fields[^2] = time.ToUnixTimeSeconds().ToString(System.Globalization.CultureInfo.InvariantCulture);
            lines[^1] = string.Join(' ', fields) + (tab < 0 ? "" : lines[^1][tab..]);
            File.WriteAllLines(log, lines);
        }

        internal ScriptedWorktreeProcessRunner CreateRunner(ProcessScript? script = null) =>
            CreateRunner(new ProductionWorktreeProcessRunner(), script);

        internal CommandResult RunWithRaw(
            IWorktreeProcessRunner runner,
            params string[] arguments) =>
            RunCore(runner, now, arguments);

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
                injectedNow);
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
