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
        Action<RegisteredWorktree>? protectObservedWorktree = null)
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

        protectObservedWorktree?.Invoke(item with
        {
            Head = actualHead,
            Branch = actualBranch.Length == 0 ? null : actualBranch,
        });
        if (!string.Equals(actualHead, item.Head, StringComparison.Ordinal)
            || !string.Equals(actualBranch, item.Branch ?? string.Empty, StringComparison.Ordinal))
        {
            return Refused("unreadable");
        }

        RegisteredWorktree? refreshed;
        try
        {
            var inventory = ReadWorktrees(repositoryRoot, runner, resolveGitDirectories: false);
            foreach (var observed in inventory) protectObservedWorktree?.Invoke(observed);
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

        if (refreshed.Locked != item.Locked || refreshed.LockReason != item.LockReason)
            return Refused(item.Locked ? "locked_changed" : "locked");
        var reason = LockAgeBlockReason(item, now) ?? ReclaimBlockReason(item, baseCommit, runner, now);
        if (reason is not null) return Refused(reason);

        try
        {
            var arguments = new List<string> { "remove", "--path", item.Path };
            arguments.Add("--expected");
            arguments.Add(System.Text.Json.JsonSerializer.Serialize(new
            {
                path = item.Path, head = item.Head,
                branch = item.Branch is null ? null : "refs/heads/" + item.Branch,
                locked = item.Locked ? item.LockReason ?? "" : null,
            }));
            var removal = WorktreeProtocolCommand.Run(repositoryRoot, arguments, runner, TimeSpan.FromSeconds(600));
            if (!removal.Success)
            {
                if (removal.ExitCode is 68 or 73) return Refused("identity_or_lock_refused");
                if (removal.Output.Length > 0)
                {
                    using var document = System.Text.Json.JsonDocument.Parse(removal.Output);
                    var outcome = document.RootElement.GetProperty("items").EnumerateArray().Single();
                    if (outcome.GetProperty("outcome").GetString() == "checkpoint_failed")
                        return new(LaneRemovalOutcome.CheckpointFailed,
                            "checkpoint_failed:" + outcome.GetProperty("error").GetString());
                }
                return new(LaneRemovalOutcome.WorktreeRemoveFailed, "worktree_remove_failed_state_indeterminate");
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new LaneRemovalResult(LaneRemovalOutcome.WorktreeRemoveFailed,
                "worktree_remove_failed_state_indeterminate");
        }

        // Keep every removed tree's branch. The invocation's observed inventory
        // also excludes these refs from its later orphan sweep.
        return new(LaneRemovalOutcome.Removed, "stale_behind");
    }

    private static string? LockAgeBlockReason(RegisteredWorktree item, DateTimeOffset now)
    {
        if (!item.Locked) return null;
        try
        {
            var file = new FileInfo(Path.Combine(item.GitDirectory!, "locked"));
            if (!file.Exists || file.LinkTarget is not null) return "locked_age_unknown";
            return now.UtcDateTime - file.LastWriteTimeUtc < TimeSpan.FromSeconds(MinimumReclaimableLaneAgeSeconds)
                ? "locked_recent" : null;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "locked_age_unknown";
        }
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
            LaneRemovalOutcome.CheckpointFailed =>
                new("stale_worktree", item.Path, item.Branch, item.Head, "failed", result.Reason),
            LaneRemovalOutcome.WorktreeRemoveFailed =>
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
        CheckpointFailed,
    }

    private sealed record LaneRemovalResult(LaneRemovalOutcome Outcome, string Reason);
}
