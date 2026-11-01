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
        var handled = idle.Select(item => item.Path).ToHashSet(StringComparer.Ordinal);
        if (idle.Length == 0) return handled;
        void PoolFailure(string reason)
        {
            events.Add(new CleanLaneEvent("idle_pool", null, null, null, "failed", reason));
            completeRemoval(inventory[0], new LaneRemovalResult(LaneRemovalOutcome.PoolSweepFailed, reason));
        }
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
        try
        {
            var arguments = new List<string> { "pool", "--dev", dev };
            if (force) arguments.Add("--force");
            var result = WorktreeProtocolCommand.Run(root, arguments, runner, Timeout.InfiniteTimeSpan);
            if (result.Output.Length == 0)
            {
                var reason = result.Error.Trim().Replace("WORKTREE_RETAINED ", string.Empty, StringComparison.Ordinal);
                if (reason.Length == 0) reason = "idle_pool_unavailable";
                PoolFailure(reason);
                return handled;
            }
            using var document = JsonDocument.Parse(result.Output);
            var failed = !result.Success || document.RootElement.GetProperty("status").GetString() == "failed";
            var reportedFailure = false;
            string? failureDiagnostic = null;
            foreach (var row in document.RootElement.GetProperty("items").EnumerateArray())
            {
                var outcome = row.GetProperty("outcome").GetString()!;
                var path = row.GetProperty("path").GetString()!;
                if (outcome == "not_idle")
                {
                    handled.Remove(path);
                    continue;
                }
                handled.Add(path);
                var observed = inventory.SingleOrDefault(item => item.Path == path);
                var item = new RegisteredWorktree(path, row.GetProperty("head").GetString()!,
                    row.GetProperty("branch").GetString()?.Replace("refs/heads/", string.Empty, StringComparison.Ordinal),
                    observed?.GitDirectory, observed?.Locked ?? false, observed?.LockReason);
                protectObservedWorktree(item);
                var reason = row.GetProperty("reason").GetString()!;
                string? ReadOptional(string name) => row.TryGetProperty(name, out var field) ? field.GetString() : null;
                var diagnostic = string.Join(":", new[] { ReadOptional("stage"), ReadOptional("error") }
                    .Where(value => !string.IsNullOrWhiteSpace(value)));
                if (diagnostic.Length != 0) failureDiagnostic = diagnostic;
                var recovery = ReadOptional("recovery_branch");
                JsonElement? nativeLocks = null;
                if (row.TryGetProperty("checkpoint", out var checkpoint) && checkpoint.ValueKind == JsonValueKind.Object
                    && checkpoint.TryGetProperty("native_locks", out var locks))
                    nativeLocks = locks.Clone();
                else if (row.TryGetProperty("native_locks", out var failedLocks))
                    nativeLocks = failedLocks.Clone();
                var removal = new LaneRemovalResult(outcome switch
                {
                    "removed" or "would_remove" => LaneRemovalOutcome.Removed,
                    "qualification_failed" => LaneRemovalOutcome.QualificationFailed,
                    "checkpoint_failed" => LaneRemovalOutcome.CheckpointFailed,
                    "partial_or_indeterminate" => LaneRemovalOutcome.WorktreeRemoveFailed,
                    "sweep_failed" => LaneRemovalOutcome.PoolSweepFailed,
                    "retained" => LaneRemovalOutcome.Refused,
                    _ => throw new InvalidOperationException("unknown idle eviction outcome: " + outcome),
                }, outcome == "sweep_failed" ? outcome + ":" + ReadOptional("stage") + ":" + ReadOptional("error")
                    : outcome is "checkpoint_failed" or "partial_or_indeterminate"
                    ? outcome + ":" + ReadOptional("error") : reason,
                    recovery, ReadOptional("recovery_branch_candidate"), NativeLocks: nativeLocks,
                    Diagnostic: diagnostic.Length == 0 ? null : diagnostic);
                reportedFailure |= removal.Outcome is LaneRemovalOutcome.QualificationFailed or LaneRemovalOutcome.CheckpointFailed
                    or LaneRemovalOutcome.WorktreeRemoveFailed or LaneRemovalOutcome.PoolSweepFailed
                    || outcome == "retained" && reason != "idle_pool";
                var removalEvent = RemovalEvent(item, removal);
                events.Add(removalEvent with
                {
                    Kind = "idle_worktree",
                    Action = outcome == "would_remove" ? "would_remove" : removalEvent.Action,
                    SelectedForRemoval = ReadOptional("stage") is "remove" or "revalidate",
                });
                if (outcome != "retained" || reason != "idle_pool") completeRemoval(item, removal);
            }
            if (document.RootElement.TryGetProperty("failure", out var poolFailure))
            {
                PoolFailure(poolFailure.GetProperty("stage").GetString() + ":"
                    + poolFailure.GetProperty("error").GetString());
            }
            else if (failed && !reportedFailure)
            {
                var diagnostic = result.Error.Trim();
                if (diagnostic.Length == 0) diagnostic = failureDiagnostic ?? string.Empty;
                PoolFailure("idle_pool_failed" + (diagnostic.Length == 0 ? string.Empty : ":" + diagnostic));
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            PoolFailure("idle_pool_failed:" + exception.GetType().Name + ":" + BoundedDiagnostic(exception.Message));
        }
        return handled;
    }
}
