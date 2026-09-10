using static StrataLint.Cli.CleanLanesCommand;

namespace StrataLint.Cli;

internal sealed record RegisteredWorktree(
    string Path,
    string Head,
    string? Branch,
    string? GitDirectory,
    bool Locked);

internal static class RegisteredWorktreeInventory
{
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
        var locked = false;
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
            else if (field == "locked" || field.StartsWith("locked ", StringComparison.Ordinal))
            {
                locked = true;
            }
            else if (field.Length == 0 && path is not null)
            {
                if (head is null)
                {
                    throw new InvalidOperationException($"worktree inventory omitted HEAD: {path}");
                }

                entries.Add(new RegisteredWorktree(
                    path,
                    head,
                    branch,
                    resolveGitDirectories ? TryResolveRegisteredGitDirectory(path, runner) : null,
                    locked));
                path = null;
                head = null;
                branch = null;
                locked = false;
            }
        }

        return entries;
    }
}
