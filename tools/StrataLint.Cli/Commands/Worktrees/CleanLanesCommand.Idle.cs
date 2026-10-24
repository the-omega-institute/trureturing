using System.Text.Json;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static IReadOnlySet<string> InspectIdlePool(string root, string? dev, bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        ICollection<CleanLaneEvent> events, IWorktreeProcessRunner runner,
        Action<RegisteredWorktree, LaneRemovalResult> completeRemoval,
        Action<RegisteredWorktree> protectObservedWorktree)
    {
        var idle = inventory.Where(item => WorktreePoolCommand.IsIdleBranch(item.Branch)).ToArray();
        var handled = new HashSet<string>(StringComparer.Ordinal);
        if (idle.Length == 0) return handled;
        if (dev is null)
        {
            foreach (var item in idle)
            {
                handled.Add(item.Path);
                events.Add(BlockedWorktree(item, "dev_unknown"));
                completeRemoval(item, Refused("dev_unknown"));
            }
            return handled;
        }
        var arguments = new List<string> { "pool", "--dev", dev };
        if (force) arguments.Add("--force");
        var result = WorktreeProtocolCommand.Run(root, arguments, runner, Timeout.InfiniteTimeSpan);
        if (result.Output.Length == 0)
        {
            var reason = result.Error.Trim().Replace("WORKTREE_RETAINED ", string.Empty, StringComparison.Ordinal);
            if (reason.Length == 0) reason = "idle_pool_unavailable";
            foreach (var item in idle)
            {
                handled.Add(item.Path);
                events.Add(BlockedWorktree(item, reason));
                completeRemoval(item, Refused(reason));
            }
            return handled;
        }
        using var document = JsonDocument.Parse(result.Output);
        foreach (var row in document.RootElement.GetProperty("items").EnumerateArray())
        {
            var outcome = row.GetProperty("outcome").GetString()!;
            if (outcome == "not_idle") continue;
            var path = row.GetProperty("path").GetString()!;
            handled.Add(path);
            var item = inventory.Single(item => item.Path == path);
            var reason = row.GetProperty("reason").GetString()!;
            string? ReadOptional(string name) => row.TryGetProperty(name, out var field) ? field.GetString() : null;
            var recovery = ReadOptional("recovery_branch");
            if (recovery is not null)
                protectObservedWorktree(item with { Branch = recovery["refs/heads/".Length..] });
            var removal = new LaneRemovalResult(outcome switch
            {
                "removed" or "would_remove" => LaneRemovalOutcome.Removed,
                "checkpoint_failed" => LaneRemovalOutcome.CheckpointFailed,
                "partial_or_indeterminate" => LaneRemovalOutcome.WorktreeRemoveFailed,
                "retained" => LaneRemovalOutcome.Refused,
                _ => throw new InvalidOperationException("unknown idle eviction outcome: " + outcome),
            }, outcome is "checkpoint_failed" or "partial_or_indeterminate"
                ? outcome + ":" + ReadOptional("error") : reason,
                recovery, ReadOptional("recovery_branch_candidate"));
            var removalEvent = RemovalEvent(item, removal);
            events.Add(removalEvent with
            {
                Kind = "idle_worktree",
                Action = outcome == "would_remove" ? "would_remove" : removalEvent.Action,
            });
            if (outcome != "retained" || reason != "idle_pool") completeRemoval(item, removal);
        }
        return handled;
    }
}
