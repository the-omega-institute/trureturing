using System.Text;
using StrataLint.Cli;
using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed partial class RemoveWorktreesCommandTests
{
    private static bool IsRemoval(WorktreeProcessInvocation call) =>
        call.FileName == "git" && call.Arguments.Take(2).SequenceEqual(["worktree", "remove"]);

    private static string Entry(string path, string? branch = null, bool locked = false) =>
        $"worktree {path}\0HEAD {new string('a', 40)}\0"
        + (branch is null ? "detached\0" : $"branch refs/heads/{branch}\0")
        + (locked ? "locked fixture lock\0" : "") + "\0";

    private sealed class InventoryRunner : IWorktreeProcessRunner
    {
        internal InventoryRunner(params string[] entries) =>
            Inventory = string.Concat(entries.Length == 0
                ? [Entry("/fixture/main", "dev"), Entry("/fixture/linked", "some-branch")]
                : entries);

        internal string Inventory { get; init; }
        internal string? InventoryFailure { get; init; }
        internal string? FailedRemovalPath { get; init; }
        internal string RemovalError { get; init; } = "fatal: removal failed\n";
        internal bool ThrowOnRemoval { get; init; }
        internal List<WorktreeProcessInvocation> Invocations { get; } = [];
        internal IEnumerable<WorktreeProcessInvocation> Removals => Invocations.Where(IsRemoval);

        public ProcessOutput Run(string fileName, IReadOnlyList<string> arguments, string workingDirectory, TimeSpan timeout)
        {
            var call = new WorktreeProcessInvocation(fileName, arguments.ToArray(), workingDirectory, timeout);
            Invocations.Add(call);
            if (fileName == "git" && arguments.SequenceEqual(["worktree", "list", "--porcelain", "-z"]))
                return InventoryFailure is null
                    ? new ProcessOutput(0, Encoding.UTF8.GetBytes(Inventory), [])
                    : new ProcessOutput(128, [], Encoding.UTF8.GetBytes(InventoryFailure));
            if (IsRemoval(call))
            {
                if (arguments[^1] != FailedRemovalPath) return new ProcessOutput(0, [], []);
                if (ThrowOnRemoval) throw new IOException(RemovalError);
                return new ProcessOutput(128, [], Encoding.UTF8.GetBytes(RemovalError));
            }
            throw new InvalidOperationException($"Unexpected process: {fileName} {string.Join(' ', arguments)}");
        }
    }

    private sealed class RemovalFixture : IDisposable
    {
        private readonly TemporaryDirectory directory = new();

        internal RemovalFixture()
        {
            Main = Path.Combine(directory.Path, "main");
            Directory.CreateDirectory(Main);
            Git(Main, "init", "--initial-branch=dev");
            Git(Main, "config", "user.name", "StrataLint Tests");
            Git(Main, "config", "user.email", "stratalint@example.invalid");
            File.WriteAllText(Path.Combine(Main, "tracked.txt"), "baseline\n");
            Git(Main, "add", "tracked.txt");
            Git(Main, "commit", "-m", "synthetic baseline");
            Main = Git(Main, "rev-parse", "--show-toplevel").Trim();
        }

        internal string Main { get; }
        internal ScriptedWorktreeProcessRunner Runner { get; } =
            new(new ProductionWorktreeProcessRunner(), static (_, _, _) => null);

        internal string Add(string name, string? branch = null)
        {
            var path = Path.Combine(directory.Path, name);
            if (branch is null) Git(Main, "worktree", "add", "--detach", path, "HEAD");
            else Git(Main, "worktree", "add", "-b", branch, path, "HEAD");
            return Git(path, "rev-parse", "--show-toplevel").Trim();
        }

        internal string CommitAndDirty(string path)
        {
            File.AppendAllText(Path.Combine(path, "tracked.txt"), "unmerged commit\n");
            Git(path, "add", "tracked.txt");
            Git(path, "commit", "-m", "branch only");
            File.AppendAllText(Path.Combine(path, "tracked.txt"), "uncommitted\n");
            File.WriteAllText(Path.Combine(path, "untracked.txt"), "untracked\n");
            return Git(path, "rev-parse", "HEAD").Trim();
        }

        internal bool BranchExists(string branch) =>
            Git(Main, "show-ref", "--verify", $"refs/heads/{branch}").Length > 0;

        internal string UnregisteredDirectory(string name) =>
            Directory.CreateDirectory(Path.Combine(directory.Path, name)).FullName;

        internal CommandResult Remove(string names) =>
            WorktreeCommand.Run(Main, ["remove", "--names", names], Runner);

        internal string Git(string root, params string[] arguments) =>
            ReviewRegressionTests.RunGit(root, arguments);

        public void Dispose() => directory.Dispose();
    }
}
