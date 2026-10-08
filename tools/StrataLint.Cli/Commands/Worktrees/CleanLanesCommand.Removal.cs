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
        LockedLaneObservation? lockedObservation = null,
        IReadOnlySet<string>? activePaths = null,
        Func<IReadOnlySet<string>?>? readHostActivity = null)
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
            var changed = LockedEvidenceBlockReason(repositoryRoot, item, baseCommit,
                Path.GetFullPath(commonDirectory, repositoryRoot), lockedObservation,
                runner, now, activePaths!, readHostActivity!);
            if (changed is not null) return Refused(changed);
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
                var inventory = ReadWorktrees(repositoryRoot, runner);
                var retained = inventory.SingleOrDefault(candidate => string.Equals(
                    candidate.Path, item.Path, StringComparison.Ordinal));
                string? changed = null;
                if (retained is null || !retained.Locked || retained.LockReason != item.LockReason)
                    changed = "locked_changed";
                else if (retained.Head != item.Head || retained.Branch != item.Branch
                    || retained.GitDirectory != item.GitDirectory) changed = "identity_changed";
                else if (PathsEqual(retained.Path, repositoryRoot)
                    || PathsEqual(retained.GitDirectory!, ResolveGitDirectory(repositoryRoot, runner))
                    || PathsEqual(retained.GitDirectory!, ResolveCommonGitDirectory(repositoryRoot, runner)))
                    changed = "protected_changed";
                else if (inventory.Any(candidate => IsNestedWorktree(item.Path, candidate.Path)))
                    changed = "nested_worktree";
                else
                {
                    changed = LockedEvidenceBlockReason(repositoryRoot, retained, baseCommit,
                        ResolveCommonGitDirectory(repositoryRoot, runner), lockedObservation,
                        runner, now, activePaths!, readHostActivity!);
                    changed ??= ReclaimBlockReason(retained, baseCommit, runner, now) is null
                        ? null : "eligibility_changed";
                }
                if (changed is not null)
                    return Refused(changed);
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                return Refused("unreadable");
            }
        }

        try
        {
            RunGit(
                repositoryRoot,
                lockedObservation is null
                    ? ["worktree", "remove", "--force", "--", item.Path]
                    : ["worktree", "remove", "--force", "--force", "--", item.Path],
                runner,
                "could not remove stale worktree");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new LaneRemovalResult(LaneRemovalOutcome.WorktreeRemoveFailed,
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

    private static string? LockedEvidenceBlockReason(
        string repositoryRoot,
        RegisteredWorktree item,
        string baseCommit,
        string commonDirectory,
        LockedLaneObservation observation,
        IWorktreeProcessRunner runner,
        DateTimeOffset now,
        IReadOnlySet<string> activePaths,
        Func<IReadOnlySet<string>?> readHostActivity)
    {
        if (!item.Locked || FileState(Path.Combine(item.GitDirectory!, "locked")) != observation.LockFingerprint)
            return "locked_changed";
        var evidence = TryReadInitializationEvidence(item, commonDirectory);
        if (evidence is null || evidence != observation.EvidenceFingerprint) return "evidence_changed";
        var activity = TryReadIndexLockActivity(item.GitDirectory!, now, out var active);
        if (activity is null || active || activity != observation.ActivityFingerprint) return "activity_changed";
        var history = TryReadHistoryFingerprint(item, commonDirectory);
        if (history is null || history != observation.HistoryFingerprint
            || ProbeRetainedHistory(repositoryRoot, item, baseCommit, commonDirectory, runner) != ContentProbeResult.Verified)
            return "history_changed";
        if (TryReadHeadContentFingerprint(item, runner, out var content) != ContentProbeResult.Verified
            || content != observation.ContentFingerprint) return "content_changed";
        return HostActivityBlockReason(item, activePaths, readHostActivity);
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
