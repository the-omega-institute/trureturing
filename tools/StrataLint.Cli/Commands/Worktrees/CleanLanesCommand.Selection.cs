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
        var updated = ReadLastUpdate(item, runner);
        if (updated is null)
            return new("update_unknown", "update_unknown", "head_commit_unreadable");
        var merged = IsAncestor(item.Path, item.Head, devCommit, runner);
        if (merged is null)
            return new("merged_state_unknown", "merged_state_unknown");

        var log = ReadAllocationLog(Path.Combine(item.GitDirectory!, "logs", "HEAD"), item.Head, treeLog: true);
        if (log.Error is not null)
            return new("update_unknown", "update_unknown", log.Error);
        var allocated = log.Allocated!.Value;
        var branches = AllocationBranches(log, item.Branch);
        foreach (var branch in branches)
        {
            AllocationLog branchLog;
            try
            {
                var common = ResolveCommonGitDirectory(item.Path, runner);
                var path = Path.Combine(common, "logs", "refs", "heads", branch);
                if (branch != item.Branch && !HasLocalAllocationEvidence(item.Path, branch, path, runner))
                {
                    // Deleted or renamed branches can share a spelling with a surviving revision.
                    // Bound this historical ambiguity by the checkout's own allocation grace.
                    allocated = Math.Max(allocated, log.Checkouts![branch].Max(static entry => entry.Updated));
                    continue;
                }
                var tip = branch == item.Branch ? item.Head
                    : ResolveCommit(item.Path, "refs/heads/" + branch, runner);
                branchLog = ReadAllocationLog(path, tip);
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                return new("update_unknown", "update_unknown", "branch_reflog_unreadable");
            }
            if (branchLog.Error is not null)
                return new("update_unknown", "update_unknown", "branch_" + branchLog.Error);
            var creation = branchLog.FirstRecord!;
            if (creation.Updated > now.ToUnixTimeSeconds())
                return new("age_unverifiable", "age_unverifiable");
            if (creation.OldHead.All(static c => c == '0'))
            {
                if (log.Checkouts!.TryGetValue(branch, out var entries)
                    && entries.Any(entry => entry.Updated == creation.Updated && entry.NewHead == creation.NewHead))
                    allocated = Math.Max(allocated, creation.Updated);
            }
            else if (creation.Updated > allocated)
                return new("update_unknown", "update_unknown", "branch_allocation_unverifiable");
        }
        var ageAnchor = Math.Max(updated.Value, allocated);

        if (merged.Value)
        {
            var clean = ReadWorktreeClean(item, runner);
            if (clean is null) return new("unreadable", "unreadable");
            if (clean.Value)
                return new(UpdateAgeBlockReason(ageAnchor, MinimumMergedLaneAgeSeconds, now),
                    "merged_to_dev", null, LockModifiedTicks(item));
        }

        var reason = OriginalReclaimBlockReason(item, baseCommit!, ageAnchor, runner, now);
        return new(reason, "original_selectors", null, LockModifiedTicks(item));
    }

    private static bool HasLocalAllocationEvidence(
        string root, string branch, string logPath, IWorktreeProcessRunner runner)
    {
        if (File.Exists(logPath) || new FileInfo(logPath).LinkTarget is not null) return true;
        var reference = "refs/heads/" + branch;
        var references = Decode(RunGit(root, ["for-each-ref", "--format=%(refname)", reference],
            runner, "could not inspect allocation branch identity").StandardOutput);
        return references.Split('\n', StringSplitOptions.RemoveEmptyEntries).Contains(reference, StringComparer.Ordinal);
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

    private static AllocationLog ReadAllocationLog(string path, string observedHead, bool treeLog = false)
    {
        try
        {
            var file = new FileInfo(path);
            if (!file.Exists) return new(Error: "reflog_missing");
            if (file.LinkTarget is not null) return new(Error: "reflog_invalid");
            var bytes = File.ReadAllBytes(path);
            using var reader = new StringReader(Decode(bytes));
            long? allocated = null;
            string? newHead = null;
            var checkouts = new Dictionary<string, List<HeadLogRecord>>(StringComparer.Ordinal);
            var explicitAllocation = false;
            HeadLogRecord? firstRecord = null;
            while (reader.ReadLine() is { } line)
            {
                if (!TryParseHeadLogRecord(line, out var record)) return new(Error: "reflog_invalid");
                firstRecord ??= record;
                allocated ??= record!.Updated;
                newHead = record!.NewHead;
                const string allocationPrefix = "worktree-allocation:";
                if (treeLog && record.Message.StartsWith(allocationPrefix, StringComparison.Ordinal))
                {
                    var token = record.Message[allocationPrefix.Length..];
                    if (token.Length != 32 || token.Any(static c => c is not (>= '0' and <= '9' or >= 'a' and <= 'f'))
                        || record.OldHead != record.NewHead)
                        return new(Error: "allocation_record_invalid");
                    allocated = Math.Max(allocated.Value, record.Updated);
                    explicitAllocation = true;
                    checkouts.Clear();
                }
                const string prefix = "checkout: moving from ";
                if (treeLog && record.Message.StartsWith(prefix, StringComparison.Ordinal)
                    && record.Message.LastIndexOf(" to ", StringComparison.Ordinal) is var separator
                    && separator >= prefix.Length)
                {
                    var branch = record.Message[(separator + 4)..];
                    if (IsAllocationBranchName(branch))
                    {
                        if (!checkouts.TryGetValue(branch, out var entries)) checkouts.Add(branch, entries = []);
                        entries.Add(record);
                    }
                }
            }
            if (allocated is null) return new(Error: "reflog_empty");
            if (!string.Equals(newHead, observedHead, StringComparison.Ordinal))
                return new(Error: "reflog_head_mismatch");
            return new(allocated, Checkouts: checkouts, ExplicitAllocation: explicitAllocation, FirstRecord: firstRecord);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new(Error: "reflog_invalid");
        }
    }

    private static IEnumerable<string> AllocationBranches(AllocationLog log, string? attached)
    {
        var branches = new HashSet<string>(log.Checkouts!.Keys, StringComparer.Ordinal);
        if (attached is not null && !log.ExplicitAllocation) branches.Add(attached);
        return branches;
    }

    private static bool IsAllocationBranchName(string value) =>
        value.Length != 0 && value != "HEAD"
        && value[0] != '/' && value[^1] is not ('/' or '.')
        && !value.Contains("..", StringComparison.Ordinal)
        && !value.Contains("@{", StringComparison.Ordinal)
        && !value.Any(static c => c <= ' ' || c is '~' or '^' or ':' or '?' or '*' or '[' or '\\' or '\u007f')
        && value.Split('/').All(static part => part.Length != 0 && part[0] != '.'
            && !part.EndsWith(".lock", StringComparison.Ordinal));

    private sealed record AllocationLog(long? Allocated = null, string? Error = null,
        Dictionary<string, List<HeadLogRecord>>? Checkouts = null, bool ExplicitAllocation = false,
        HeadLogRecord? FirstRecord = null);

    private sealed record ReclaimSelection(string? BlockReason, string Reason,
        string? Detail = null, long? LockModifiedTicks = null)
    {
        internal string RemovalReason(bool locked = false) =>
            Reason == "merged_to_dev" ? Reason : locked ? "stale_lock" : "stale_behind";
    }
}
