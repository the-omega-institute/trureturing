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
        RegisteredWorktree item, string? baseCommit, string? devCommit,
        IWorktreeProcessRunner runner, DateTimeOffset now)
    {
        if (devCommit is null) return new("dev_unknown", "dev_unknown");
        var merged = IsAncestor(item.Path, item.Head, devCommit, runner);
        if (merged is null)
            return new("merged_state_unknown", "merged_state_unknown");

        var log = ReadHeadLog(item.GitDirectory!, item.Head);
        if (log.Error is not null)
            return new("update_unknown", "update_unknown", log.Error);
        var updated = ReadLastUpdate(item, log.Updated!.Value, runner);
        if (updated is null)
            return new("update_unknown", "update_unknown");

        if (merged.Value)
        {
            var clean = ReadWorktreeClean(item, runner);
            if (clean is null) return new("unreadable", "unreadable");
            if (clean.Value)
                return new(UpdateAgeBlockReason(updated.Value, MinimumMergedLaneAgeSeconds, now),
                    "merged_to_dev", null, LockModifiedTicks(item));
        }

        var reason = OriginalReclaimBlockReason(item, baseCommit!, updated.Value, runner, now);
        return new(reason, "original_selectors", null, LockModifiedTicks(item));
    }

    private static long? LockModifiedTicks(RegisteredWorktree item) => item.Locked
        ? File.GetLastWriteTimeUtc(Path.Combine(item.GitDirectory!, "locked")).Ticks : null;

    private static bool? ReadWorktreeClean(RegisteredWorktree item, IWorktreeProcessRunner runner)
    {
        try
        {
            var operations = new[] { "MERGE_HEAD", "CHERRY_PICK_HEAD", "REVERT_HEAD", "rebase-merge", "rebase-apply", "sequencer" }
                .Where(marker => Path.Exists(Path.Combine(item.GitDirectory!, marker))).ToArray();
            var status = RunGit(item.Path,
                ["status", "--porcelain=v1", "-z", "--untracked-files=all", "--ignore-submodules=none"],
                runner, "could not inspect worktree changes").StandardOutput;
            return status.Length == 0 && operations.Length == 0;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static HeadLog ReadHeadLog(string gitDirectory, string observedHead)
    {
        try
        {
            var path = Path.Combine(gitDirectory, "logs", "HEAD");
            var file = new FileInfo(path);
            if (!file.Exists) return new(Error: "reflog_missing");
            if (file.LinkTarget is not null) return new(Error: "reflog_invalid");
            var bytes = File.ReadAllBytes(path);
            using var reader = new StringReader(Decode(bytes));
            long? updated = null;
            string? newHead = null;
            while (reader.ReadLine() is { } line)
            {
                if (!TryParseHeadLogRecord(line, out var record)) return new(Error: "reflog_invalid");
                updated = Math.Max(updated ?? record!.Updated, record!.Updated);
                newHead = record.NewHead;
            }
            if (updated is null) return new(Error: "reflog_empty");
            if (!string.Equals(newHead, observedHead, StringComparison.Ordinal))
                return new(Error: "reflog_head_mismatch");
            return new(updated);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(Error: "reflog_invalid");
        }
    }

    private sealed record HeadLog(long? Updated = null, string? Error = null);

    private sealed record ReclaimSelection(string? BlockReason, string Reason,
        string? Detail = null, long? LockModifiedTicks = null)
    {
        internal string RemovalReason(bool locked = false) =>
            Reason == "merged_to_dev" ? Reason : locked ? "stale_lock" : "stale_behind";
    }
}
