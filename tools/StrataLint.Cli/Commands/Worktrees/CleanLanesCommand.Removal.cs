using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static string? RemoveLane(
        string repositoryRoot,
        RegisteredWorktree item,
        IWorktreeProcessRunner runner,
        LaneProcessProbe laneProcessProbe)
    {
        var actualHead = Decode(RunGit(
            item.Path,
            ["rev-parse", "--verify", "HEAD^{commit}"],
            runner,
            "could not re-read lane head").StandardOutput).Trim();
        var actualBranch = Decode(RunGit(
            item.Path,
            ["branch", "--show-current"],
            runner,
            "could not re-read lane branch").StandardOutput).Trim();
        if (!string.Equals(actualHead, item.Head, StringComparison.Ordinal)
            || !string.Equals(actualBranch, item.Branch, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"lane identity changed during cleanup: {item.Path}");
        }

        var finalStatus = RunGit(
            item.Path,
            ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
            runner,
            "could not re-read lane status");
        if (finalStatus.StandardOutput.Length != 0)
        {
            throw new InvalidOperationException($"lane became dirty during cleanup: {item.Path}");
        }

        var refreshed = ReadWorktrees(repositoryRoot, runner)
            .SingleOrDefault(candidate => string.Equals(
                candidate.Path,
                item.Path,
                StringComparison.Ordinal));
        if (refreshed is null)
        {
            throw new InvalidOperationException($"lane identity changed during cleanup: {item.Path}");
        }

        if (refreshed.Locked) return "locked";

        LaneProcessProbeOutcome processProbe;
        try
        {
            processProbe = laneProcessProbe(CanonicalPath(item.Path), runner);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "in_use_unknown";
        }

        if (!processProbe.Success) return "in_use_unknown";
        if (processProbe.InUse) return "in_use";

        RunGit(
            repositoryRoot,
            ["worktree", "remove", item.Path],
            runner,
            "could not remove merged lane worktree");
        DeleteObservedRef(repositoryRoot, item.Branch!, item.Head, runner);
        return null;
    }
}
