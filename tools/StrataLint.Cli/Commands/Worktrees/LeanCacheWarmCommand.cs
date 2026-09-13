namespace StrataLint.Cli;

internal static class LeanCacheWarmCommand
{
    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner)
    {
        if (!LeanCacheEnsureCommand.TryParse(repositoryRoot, arguments, false, out var root, out _))
            return new(false, string.Empty, "USAGE: StrataLint worktree warm-cache [--path DIR]\n");
        return LeanCacheEnsureCommand.Run(repositoryRoot,
            ["--path", root, "--", "lake", "build"], runner, runCommand: true);
    }
}
