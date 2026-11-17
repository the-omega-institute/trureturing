using static StrataLint.Cli.CleanLanesCommand;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal sealed record RegisteredWorktree(
    string Path,
    string Head,
    string? Branch,
    string? GitDirectory,
    string? IdentityFailure = null);

internal static class RegisteredWorktreeInventory
{
    private sealed record GitDirectoryObservation(string? GitDirectory, string? Failure);

    internal static IReadOnlyList<RegisteredWorktree> ReadWorktrees(
        string repositoryRoot,
        IWorktreeProcessRunner runner,
        bool resolveGitDirectories = true)
    {
        var result = RunGit(
            repositoryRoot,
            ["worktree", "list", "--porcelain", "-z"],
            runner,
            "could not enumerate git worktrees");
        var entries = new List<RegisteredWorktree>();
        string? path = null;
        string? head = null;
        string? branch = null;
        foreach (var field in Decode(result.StandardOutput).Split('\0'))
        {
            if (field.StartsWith("worktree ", StringComparison.Ordinal))
            {
                path = Path.GetFullPath(field["worktree ".Length..]);
            }
            else if (field.StartsWith("HEAD ", StringComparison.Ordinal))
            {
                head = field["HEAD ".Length..];
            }
            else if (field.StartsWith("branch refs/heads/", StringComparison.Ordinal))
            {
                branch = field["branch refs/heads/".Length..];
            }
            else if (field.Length == 0 && path is not null)
            {
                if (head is null)
                {
                    throw new InvalidOperationException($"worktree inventory omitted HEAD: {path}");
                }

                var observation = resolveGitDirectories ? ObserveRegisteredGitDirectory(path, runner) : new GitDirectoryObservation(null, null);
                entries.Add(new RegisteredWorktree(
                    path,
                    head,
                    branch,
                    observation.GitDirectory,
                    observation.Failure));
                path = null;
                head = null;
                branch = null;
            }
        }

        return entries;
    }

    private static GitDirectoryObservation ObserveRegisteredGitDirectory(string path, IWorktreeProcessRunner runner)
    {
        var result = runner.Run("git", ["rev-parse", "--absolute-git-dir"], path,
            BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode != 0)
            return new(null, CleanLanesCommand.Decode(result.StandardError));
        return new(Path.GetFullPath(CleanLanesCommand.Decode(result.StandardOutput).Trim()), null);
    }
}
