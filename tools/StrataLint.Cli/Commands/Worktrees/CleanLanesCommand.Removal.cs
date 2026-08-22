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
        string actualHead;
        try
        {
            actualHead = Decode(RunGit(
                item.Path,
                ["rev-parse", "--verify", "HEAD^{commit}"],
                runner,
                "could not re-read lane head").StandardOutput).Trim();
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "unreadable";
        }

        string actualBranch;
        try
        {
            actualBranch = Decode(RunGit(
                item.Path,
                ["branch", "--show-current"],
                runner,
                "could not re-read lane branch").StandardOutput).Trim();
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "unreadable";
        }

        if (!string.Equals(actualHead, item.Head, StringComparison.Ordinal)
            || !string.Equals(actualBranch, item.Branch, StringComparison.Ordinal))
        {
            return "unreadable";
        }

        ProcessOutput finalStatus;
        try
        {
            finalStatus = RunGit(
                item.Path,
                ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
                runner,
                "could not re-read lane status");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "unreadable";
        }

        if (finalStatus.StandardOutput.Length != 0)
        {
            return "dirty";
        }

        RegisteredWorktree? refreshed;
        try
        {
            refreshed = ReadWorktrees(repositoryRoot, runner)
                .SingleOrDefault(candidate => string.Equals(
                    candidate.Path,
                    item.Path,
                    StringComparison.Ordinal));
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "unreadable";
        }

        if (refreshed is null) return "unreadable";

        if (!string.Equals(refreshed.Head, item.Head, StringComparison.Ordinal)
            || !string.Equals(refreshed.Branch, item.Branch, StringComparison.Ordinal))
        {
            return "unreadable";
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
