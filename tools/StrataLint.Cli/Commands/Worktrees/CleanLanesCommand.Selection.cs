using System.Security.Cryptography;
using System.Text;

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
            return new("work_witness_unknown", "work_witness_unknown", log.Error);
        var witnessReason = WorkWitnessReason(item, log, runner);
        if (witnessReason == "head_commit_unreadable")
            return new("work_witness_unknown", "work_witness_unknown", witnessReason, log.Fingerprint);

        var selectionReason = merged.Value && witnessReason is not null
            ? "merged_without_work_witness" : "original_selectors";
        if (merged.Value && witnessReason is null)
        {
            var clean = ReadWorktreeClean(item, runner);
            if (clean is null) return new("unreadable", "unreadable", null, log.Fingerprint);
            if (clean.Value)
                return new(null, "merged_to_dev", null, log.Fingerprint, LockModifiedTicks(item));
        }

        var reason = OriginalReclaimBlockReason(item, baseCommit!, log.Updated!.Value, runner, now);
        return new(reason, selectionReason, witnessReason, log.Fingerprint, LockModifiedTicks(item));
    }

    private static long? LockModifiedTicks(RegisteredWorktree item) => item.Locked
        ? File.GetLastWriteTimeUtc(Path.Combine(item.GitDirectory!, "locked")).Ticks : null;

    private static string? WorkWitnessReason(
        RegisteredWorktree item, HeadLog log, IWorktreeProcessRunner runner)
    {
        if (log.OldHead!.All(static c => c == '0')) return "initial_head";
        if (string.Equals(log.OldHead, item.Head, StringComparison.Ordinal)) return "head_unchanged";
        var message = log.Message!;
        var colon = message.IndexOf(':');
        if (colon < 0) return "head_event_not_work";
        var action = message[..colon];
        var merge = (action == "merge" || action.StartsWith("merge ", StringComparison.Ordinal))
            && message[(colon + 1)..].StartsWith(" Merge made by ", StringComparison.Ordinal);
        var produced = action is "commit" or "commit (amend)" or "commit (merge)" or "cherry-pick"
            || action.StartsWith("rebase ", StringComparison.Ordinal)
                && (action.EndsWith(" (finish)", StringComparison.Ordinal)
                    || action.EndsWith(" (pick)", StringComparison.Ordinal));
        if (!produced && !merge) return "head_event_not_work";
        try
        {
            var type = Decode(RunGit(item.Path, ["cat-file", "-t", item.Head], runner,
                "could not read witnessed commit").StandardOutput).Trim();
            if (type != "commit") return "head_commit_unreadable";
            if (merge)
            {
                var parents = Decode(RunGit(item.Path, ["rev-list", "--parents", "--max-count=1", item.Head],
                    runner, "could not read merge parents").StandardOutput)
                    .Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries);
                if (parents.Length < 3) return "merge_without_merge_commit";
                if (parents[0] != item.Head || !parents.All(IsObjectOid)) return "head_commit_unreadable";
            }
            return null;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "head_commit_unreadable";
        }
    }

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
            string? oldHead = null;
            string? newHead = null;
            string? message = null;
            string? lastLine = null;
            while (reader.ReadLine() is { } line)
            {
                if (!TryParseHeadLogRecord(line, out var record)) return new(Error: "reflog_invalid");
                updated = Math.Max(updated ?? record!.Updated, record!.Updated);
                oldHead = record.OldHead;
                newHead = record.NewHead;
                message = record.Message;
                lastLine = line;
            }
            if (updated is null) return new(Error: "reflog_empty");
            if (!string.Equals(newHead, observedHead, StringComparison.Ordinal))
                return new(Error: "reflog_head_mismatch");
            return new(updated, oldHead, message,
                Convert.ToHexString(SHA256.HashData(Encoding.UTF8.GetBytes(lastLine!))).ToLowerInvariant());
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(Error: "reflog_invalid");
        }
    }

    private sealed record HeadLog(long? Updated = null, string? OldHead = null,
        string? Message = null, string? Fingerprint = null, string? Error = null);

    private sealed record ReclaimSelection(string? BlockReason, string Reason,
        string? WitnessReason = null, string? ReflogFingerprint = null,
        long? LockModifiedTicks = null)
    {
        internal string RemovalReason(bool locked = false) =>
            Reason == "merged_to_dev" ? Reason : locked ? "stale_lock" : "stale_behind";
    }
}
