using static StrataLint.Cli.RegisteredWorktreeInventory;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static LaneRemovalResult RemoveLane(
        string repositoryRoot,
        RegisteredWorktree item,
        string baseCommit,
        IWorktreeProcessRunner runner,
        DateTimeOffset now,
        LockedLaneObservation? lockedObservation = null)
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
            || !string.Equals(actualBranch, item.Branch ?? string.Empty, StringComparison.Ordinal))
        {
            return Refused("unreadable");
        }

        RegisteredWorktree? refreshed;
        try
        {
            var inventory = ReadWorktrees(repositoryRoot, runner, resolveGitDirectories: false);
            if (inventory.Any(candidate => IsNestedWorktree(item.Path, candidate.Path)))
                return Refused("nested_worktree");
            refreshed = inventory.SingleOrDefault(candidate => string.Equals(
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

        if (lockedObservation is null)
        {
            if (refreshed.Locked) return Refused("locked");
        }
        else
        {
            if (!refreshed.Locked
                || !string.Equals(refreshed.LockReason, item.LockReason, StringComparison.Ordinal))
                return Refused("locked_changed");

            var commonDirectory = Decode(RunGit(
                repositoryRoot,
                ["rev-parse", "--git-common-dir"],
                runner,
                "could not resolve common Git directory").StandardOutput).Trim();
            var evidence = TryReadInitializationEvidence(
                item,
                Path.GetFullPath(commonDirectory, repositoryRoot));
            if (evidence is null
                || !string.Equals(evidence, lockedObservation.EvidenceFingerprint, StringComparison.Ordinal))
                return Refused("evidence_changed");

            var activity = TryReadIndexLockActivity(
                item.GitDirectory!,
                now,
                out var active);
            if (activity is null || active
                || !string.Equals(activity, lockedObservation.ActivityFingerprint, StringComparison.Ordinal))
                return Refused("activity_changed");

            var history = TryReadHistoryFingerprint(item.GitDirectory!);
            if (history is null
                || !string.Equals(history, lockedObservation.HistoryFingerprint, StringComparison.Ordinal))
                return Refused("history_changed");

            var contentResult = TryReadHeadContentFingerprint(item, runner, out var content);
            if (contentResult != ContentProbeResult.Verified
                || !string.Equals(content, lockedObservation.ContentFingerprint, StringComparison.Ordinal))
                return Refused("content_changed");
        }

        var reason = ReclaimBlockReason(item, baseCommit, runner, now);
        if (reason is not null)
        {
            return Refused(lockedObservation is null
                ? reason
                : reason switch
                {
                    "recently_updated" or "age_unverifiable" => "activity_changed",
                    _ => "eligibility_changed",
            });
        }

        if (lockedObservation is not null)
        {
            try
            {
                RunGit(
                    repositoryRoot,
                    ["worktree", "unlock", item.Path],
                    runner,
                    "could not unlock stale initialization worktree");
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                return Refused("unlock_failed");
            }

            var unlocked = ReadWorktrees(repositoryRoot, runner, resolveGitDirectories: false)
                .SingleOrDefault(candidate => string.Equals(
                    candidate.Path,
                    item.Path,
                    StringComparison.Ordinal));
            if (unlocked is null || unlocked.Locked) return Refused("locked_changed");
        }

        try
        {
            RunGit(
                repositoryRoot,
                ["worktree", "remove", "--force", "--", item.Path],
                runner,
                "could not remove stale worktree");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(
                LaneRemovalOutcome.WorktreeRemoveFailed,
                "worktree_remove_failed_state_indeterminate");
        }

        try
        {
            if (item.Branch is not null && WorktreeCommand.IsManagedBranch(item.Branch))
            {
                DeleteObservedRef(repositoryRoot, item.Branch, item.Head, runner);
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(LaneRemovalOutcome.BranchRefRetained, "branch_ref_retained");
        }

        return new(LaneRemovalOutcome.Removed, "stale_behind");
    }

    private static LaneRemovalResult Refused(string reason) =>
        new(LaneRemovalOutcome.Refused, reason);

    private static CleanLaneEvent RemovalEvent(
        RegisteredWorktree item,
        LaneRemovalResult result) =>
        result.Outcome switch
        {
            LaneRemovalOutcome.Refused =>
                BlockedWorktree(item, result.Reason),
            LaneRemovalOutcome.Removed =>
                new("stale_worktree", item.Path, item.Branch, item.Head, "removed", result.Reason),
            LaneRemovalOutcome.WorktreeRemoveFailed or LaneRemovalOutcome.BranchRefRetained =>
                new(
                    "stale_worktree",
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
