namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static string? TryResolveDevCommit(string root, IWorktreeProcessRunner runner)
    {
        try
        {
            var commit = ResolveCommit(root, "refs/remotes/origin/dev", runner);
            return IsObjectOid(commit) && commit.Any(static c => c != '0') ? commit : null;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static ReclaimSelection SelectForReclaim(
        RegisteredWorktree item, IWorktreeProcessRunner runner, DateTimeOffset now)
    {
        if (ReadRemovalPending(item, runner))
            return new(null, "interrupted_removal", null, LockModifiedTicks(item));
        var updated = ReadLastUpdate(item, runner);
        if (updated is null)
            return new("update_unknown", "update_unknown", "head_commit_unreadable");
        return new(UpdateAgeBlockReason(updated.Value, now), "head_commit_age", null, LockModifiedTicks(item));
    }

    private static bool ReadRemovalPending(RegisteredWorktree item, IWorktreeProcessRunner runner)
    {
        if (!File.Exists(Path.Combine(item.GitDirectory!, "worktree-removal"))) return false;
        try
        {
            var result = WorktreeProtocolCommand.Run(item.Path,
                ["removal-pending", "--path", item.Path], runner);
            if (!result.Success) return false;
            using var document = System.Text.Json.JsonDocument.Parse(result.Output);
            var row = document.RootElement;
            return row.GetProperty("event").GetString() == "worktree_removal_pending"
                && row.GetProperty("path").GetString() == item.Path
                && row.GetProperty("commit").GetString() == item.Head
                && row.GetProperty("pending").GetBoolean();
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return false;
        }
    }

    private static long? LockModifiedTicks(RegisteredWorktree item) => item.Locked
        ? File.GetLastWriteTimeUtc(Path.Combine(item.GitDirectory!, "locked")).Ticks : null;

    private sealed record ReclaimSelection(string? BlockReason, string Reason,
        string? Detail = null, long? LockModifiedTicks = null)
    {
        internal string RemovalReason() => Reason;
    }
}
