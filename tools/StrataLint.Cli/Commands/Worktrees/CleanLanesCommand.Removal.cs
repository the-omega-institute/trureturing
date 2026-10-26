using static StrataLint.Cli.RegisteredWorktreeInventory;
using StrataLint.Engine;
using StrataLint.Runtime;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static LaneRemovalResult RemoveLane(
        string repositoryRoot,
        RegisteredWorktree item,
        string? baseCommit,
        string? devCommit,
        ReclaimSelection selection,
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
            return IdentityReadFailure(item, exception);
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
            return IdentityReadFailure(item, exception);
        }

        protectObservedWorktree?.Invoke(item with
        {
            Head = actualHead,
            Branch = actualBranch.Length == 0 ? null : actualBranch,
        });
        if (!string.Equals(actualHead, item.Head, StringComparison.Ordinal)
            || !string.Equals(actualBranch, item.Branch ?? string.Empty, StringComparison.Ordinal))
        {
            return Refused("race_changed");
        }

        RegisteredWorktree? refreshed;
        try
        {
            var inventory = ReadWorktrees(repositoryRoot, runner, resolveGitDirectories: false);
            foreach (var observed in inventory) protectObservedWorktree?.Invoke(observed);
            if (inventory.Any(candidate => IsNestedWorktree(item.Path, candidate.Path)))
                return Refused("race_changed");
            refreshed = inventory.SingleOrDefault(candidate => string.Equals(
                    candidate.Path,
                    item.Path,
                    StringComparison.Ordinal));
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return IdentityReadFailure(item, exception);
        }

        if (refreshed is null) return Refused("race_changed");

        if (!string.Equals(refreshed.Head, item.Head, StringComparison.Ordinal)
            || !string.Equals(refreshed.Branch, item.Branch, StringComparison.Ordinal))
        {
            return Refused("race_changed");
        }

        if (refreshed.Locked != item.Locked || refreshed.LockReason != item.LockReason)
            return Refused("race_changed");
        var observation = ObserveRegisteredGitDirectory(item.Path, runner);
        if (observation.Failure is not null)
            return new(LaneRemovalOutcome.QualificationFailed, observation.Failure);
        if (!string.Equals(observation.GitDirectory, item.GitDirectory, StringComparison.Ordinal))
            return Refused("race_changed");
        var refreshedSelection = SelectForReclaim(item, baseCommit, devCommit, runner, now);
        if (refreshedSelection != selection) return Refused("race_changed");
        var reason = refreshedSelection.BlockReason;
        if (reason is not null) return Refused(reason);

        string? recoveryBranch = null;
        string? recoveryBranchCandidate = null;
        System.Text.Json.JsonElement? nativeLocks = null;
        CommandResult? removal = null;
        var dispatched = false;
        try
        {
            var arguments = new List<string> { "remove", "--path", item.Path };
            arguments.Add("--expected");
            var expected = new
            {
                path = item.Path, head = item.Head,
                branch = item.Branch is null ? null : "refs/heads/" + item.Branch,
                locked = item.Locked ? item.LockReason ?? "" : null,
            };
            arguments.Add(System.Text.Json.JsonSerializer.Serialize(expected));
            dispatched = true;
            removal = WorktreeProtocolCommand.Run(repositoryRoot, arguments, runner, TimeSpan.FromSeconds(600));
            var refusal = CanonicalRefusal(removal);
            if (refusal is not null) return Refused(refusal);
            if (removal.ExitCode == 74 && removal.Output.Length == 0
                && removal.Error.StartsWith("WORKTREE_FAILED qualification_failed:", StringComparison.Ordinal))
                return new(LaneRemovalOutcome.QualificationFailed,
                    QualificationFailure(new InvalidOperationException("removal preflight failed"), removal).Reason!);
            System.Text.Json.JsonElement? outcome = null;
            if (removal.Output.Length > 0)
            {
                using var document = System.Text.Json.JsonDocument.Parse(removal.Output);
                var receipt = document.RootElement;
                outcome = receipt.GetProperty("items").EnumerateArray().Single().Clone();
                if (receipt.GetProperty("event").GetString() != "worktree_removal"
                    || outcome.Value.GetProperty("path").GetString() != item.Path)
                    throw new InvalidOperationException("invalid removal receipt");
                if (outcome.Value.TryGetProperty("recovery_branch", out var recovery))
                    recoveryBranch = recovery.GetString();
                if (outcome.Value.TryGetProperty("recovery_branch_candidate", out var candidate))
                    recoveryBranchCandidate = candidate.GetString();
                if (outcome.Value.TryGetProperty("checkpoint", out var checkpoint)
                    && checkpoint.ValueKind == System.Text.Json.JsonValueKind.Object
                    && checkpoint.TryGetProperty("native_locks", out var locks))
                    nativeLocks = locks.Clone();
                else if (outcome.Value.TryGetProperty("native_locks", out var failedLocks))
                    nativeLocks = failedLocks.Clone();
                if (outcome.Value.TryGetProperty("recovery_roots", out var roots))
                    foreach (var root in roots.EnumerateArray())
                        protectObservedWorktree?.Invoke(item with
                        {
                            Branch = root.GetString()!["refs/heads/".Length..],
                        });
                if (recoveryBranch is not null)
                    protectObservedWorktree?.Invoke(item with
                    {
                        Branch = recoveryBranch["refs/heads/".Length..],
                    });
                var state = outcome.Value.GetProperty("outcome").GetString();
                if (state == "refused" && removal.ExitCode is 68 or 73
                    && receipt.GetProperty("status").GetString() == "refused")
                {
                    var receiptReason = outcome.Value.GetProperty("reason").GetString();
                    if (string.IsNullOrWhiteSpace(receiptReason)) throw new InvalidOperationException("missing refusal reason");
                    return Refused(receiptReason);
                }
                if (state == "qualification_failed" && removal.ExitCode == 74
                    && receipt.GetProperty("status").GetString() == "failed")
                {
                    var receiptReason = outcome.Value.GetProperty("reason").GetString();
                    if (receiptReason is null || !receiptReason.StartsWith("qualification_failed:", StringComparison.Ordinal))
                        throw new InvalidOperationException("missing qualification failure diagnostic");
                    return new(LaneRemovalOutcome.QualificationFailed, receiptReason);
                }
                if (state is not ("removed" or "checkpoint_failed" or "partial_or_indeterminate")
                    || receipt.GetProperty("status").GetString() != (state == "removed" ? "succeeded" : "failed"))
                    throw new InvalidOperationException("inconsistent removal receipt");
            }
            if (!removal.Success)
            {
                if (outcome?.GetProperty("outcome").GetString() == "checkpoint_failed")
                    return new(LaneRemovalOutcome.CheckpointFailed,
                        "checkpoint_failed:" + outcome.Value.GetProperty("error").GetString(), recoveryBranch, recoveryBranchCandidate,
                        NativeLocks: nativeLocks);
                if (outcome is null)
                    throw new InvalidOperationException("missing removal receipt");
                return new(LaneRemovalOutcome.WorktreeRemoveFailed, "worktree_remove_failed_state_indeterminate", recoveryBranch, recoveryBranchCandidate,
                    NativeLocks: nativeLocks, Diagnostic: "exit=" + removal.ExitCode + ":stderr=" + BoundedDiagnostic(removal.Error)
                        + ":error=" + (outcome.Value.TryGetProperty("error", out var error) ? BoundedDiagnostic(error.GetString() ?? "") : ""));
            }
            if (outcome?.GetProperty("outcome").GetString() != "removed"
                || !RemovalDiagnosticsMatch(removal.Error, nativeLocks))
                throw new InvalidOperationException("missing or unsuccessful removal receipt");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            if (!dispatched || BoundedProcessRunner.FailedBeforeStart(exception))
                return new(LaneRemovalOutcome.QualificationFailed, QualificationFailure(exception, removal).Reason!);
            return new(LaneRemovalOutcome.WorktreeRemoveFailed, "worktree_remove_failed_state_indeterminate",
                recoveryBranch, recoveryBranchCandidate, NativeLocks: nativeLocks,
                Diagnostic: exception.GetType().Name + ":" + BoundedDiagnostic(exception.Message)
                    + (removal is null ? string.Empty : ":exit=" + removal.ExitCode
                        + ":stderr=" + BoundedDiagnostic(removal.Error) + ":stdout=" + BoundedDiagnostic(removal.Output)));
        }

        // Retain both observed branches and refs created for detached recovery
        // through the invocation's later orphan sweep.
        return new(LaneRemovalOutcome.Removed, selection.RemovalReason(), recoveryBranch, NativeLocks: nativeLocks);
    }

    private static bool RemovalDiagnosticsMatch(string error, System.Text.Json.JsonElement? locks)
    {
        foreach (var line in error.Split('\n', StringSplitOptions.RemoveEmptyEntries))
        {
            using var document = System.Text.Json.JsonDocument.Parse(line);
            var observation = document.RootElement;
            if (observation.GetProperty("event").GetString() != "worktree_native_lock"
                || locks is null || !locks.Value.EnumerateArray().Any(item =>
                    System.Text.Json.JsonElement.DeepEquals(item, observation))) return false;
        }
        return true;
    }

    private static LaneRemovalResult Refused(string reason) =>
        new(LaneRemovalOutcome.Refused, reason);

    private static LaneRemovalResult IdentityReadFailure(RegisteredWorktree item, Exception exception) =>
        Directory.Exists(item.Path) && HasGitMarker(item.Path)
            ? new(LaneRemovalOutcome.QualificationFailed, IdentityFailure(exception))
            : Refused("race_changed");

    private static CleanLaneEvent RemovalEvent(
        RegisteredWorktree item,
        LaneRemovalResult result) =>
        (result.Outcome switch
        {
            LaneRemovalOutcome.Refused =>
                BlockedWorktree(item, result.Reason),
            LaneRemovalOutcome.Removed =>
                new("stale_worktree", item.Path, item.Branch, item.Head, "removed", result.Reason),
            LaneRemovalOutcome.QualificationFailed or LaneRemovalOutcome.CheckpointFailed or LaneRemovalOutcome.PoolSweepFailed =>
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
        }) with { RecoveryBranch = result.RecoveryBranch, RecoveryBranchCandidate = result.RecoveryBranchCandidate,
            NativeLocks = result.NativeLocks, Diagnostic = result.Diagnostic };

    private enum LaneRemovalOutcome
    {
        Refused,
        Removed,
        WorktreeRemoveFailed,
        CheckpointFailed,
        QualificationFailed,
        PoolSweepFailed,
    }

    private sealed record LaneRemovalResult(LaneRemovalOutcome Outcome, string Reason,
        string? RecoveryBranch = null, string? RecoveryBranchCandidate = null,
        System.Text.Json.JsonElement? NativeLocks = null, string? Diagnostic = null);
}
