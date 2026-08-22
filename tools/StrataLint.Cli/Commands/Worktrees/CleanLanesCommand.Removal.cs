using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static LaneRemovalResult RemoveLane(
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
            return Refused("unreadable");
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
            return Refused("unreadable");
        }

        if (!string.Equals(actualHead, item.Head, StringComparison.Ordinal)
            || !string.Equals(actualBranch, item.Branch, StringComparison.Ordinal))
        {
            return Refused("unreadable");
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
            return Refused("unreadable");
        }

        if (finalStatus.StandardOutput.Length != 0)
        {
            return Refused("dirty");
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
            return Refused("unreadable");
        }

        if (refreshed is null) return Refused("unreadable");

        if (!string.Equals(refreshed.Head, item.Head, StringComparison.Ordinal)
            || !string.Equals(refreshed.Branch, item.Branch, StringComparison.Ordinal))
        {
            return Refused("unreadable");
        }

        if (refreshed.Locked) return Refused("locked");

        LaneProcessProbeOutcome processProbe;
        try
        {
            processProbe = laneProcessProbe(CanonicalPath(item.Path), runner);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return Refused("in_use_unknown");
        }

        if (!processProbe.Success) return Refused("in_use_unknown");
        if (processProbe.InUse) return Refused("in_use");

        try
        {
            RunGit(
                repositoryRoot,
                ["worktree", "remove", item.Path],
                runner,
                "could not remove merged lane worktree");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(LaneRemovalOutcome.WorktreeRemoveFailed, "worktree_remove_failed");
        }

        try
        {
            DeleteObservedRef(repositoryRoot, item.Branch!, item.Head, runner);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(LaneRemovalOutcome.BranchRefRetained, "branch_ref_retained");
        }

        return new(LaneRemovalOutcome.Removed, "merged_clean");
    }

    private static LaneRemovalResult Refused(string reason) =>
        new(LaneRemovalOutcome.Refused, reason);

    private static CleanLaneEvent RemovalEvent(
        RegisteredWorktree item,
        LaneRemovalResult result) =>
        result.Outcome switch
        {
            LaneRemovalOutcome.Refused or LaneRemovalOutcome.WorktreeRemoveFailed =>
                BlockedWorktree(item, result.Reason),
            LaneRemovalOutcome.Removed =>
                new("merged_worktree", item.Path, item.Branch, item.Head, "removed", result.Reason),
            LaneRemovalOutcome.BranchRefRetained =>
                new(
                    "merged_worktree",
                    item.Path,
                    item.Branch,
                    item.Head,
                    "partially_removed",
                    result.Reason),
            _ => throw new InvalidOperationException($"unknown lane removal outcome: {result.Outcome}"),
        };

    private enum LaneRemovalOutcome
    {
        Refused,
        Removed,
        WorktreeRemoveFailed,
        BranchRefRetained,
    }

    private sealed record LaneRemovalResult(LaneRemovalOutcome Outcome, string Reason);
}
