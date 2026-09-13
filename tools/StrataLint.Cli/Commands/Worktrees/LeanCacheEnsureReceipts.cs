using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

// ensure 的收据渲染。与状态机正交：状态机决定「发生了什么」，这里只决定「怎么写下来」。
// 拆出来是因为 LeanCacheEnsureCommand.cs 触到了 SL-003 的 800 行硬线（第 8 条：桶满则裂）。
internal static partial class LeanCacheEnsureCommand
{
    private static CommandResult SuccessReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? pinSha256,
        string? reason,
        MathlibOleanInventory mathlibOleans,
        string? stampMiss = null,
        ClonefileReceipt? clonefile = null,
        LeanArchiveAttempt? archive = null) =>
        new(
            true,
            RenderReceipt(
                status,
                worktree,
                donor,
                method,
                pinSha256,
                reason,
                mathlibOleans,
                stampMiss,
                clonefile,
                archive),
            string.Empty);

    private static CommandResult FailureReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? pinSha256,
        string reason,
        string? stampMiss = null,
        ClonefileReceipt? clonefile = null) =>
        new(
            false,
            string.Empty,
            RenderReceipt(
                status,
                worktree,
                donor,
                method,
                pinSha256,
                reason,
                MathlibOleanInventory.Unknown,
                stampMiss,
                clonefile));

    private static CommandResult RefusedSymlink(string root, string pinSha256) =>
        FailureReceipt(
            "refused",
            root,
            donor: null,
            method: "none",
            pinSha256,
            reason: ".lake is a symlink; shared Lean caches are forbidden");

    private static bool TryParseWorktreeRoot(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        out string root)
    {
        var path = repositoryRoot;
        if (arguments.Count != 0)
        {
            if (arguments.Count != 2
                || !string.Equals(arguments[0], "--path", StringComparison.Ordinal)
                || string.IsNullOrWhiteSpace(arguments[1]))
            {
                root = string.Empty;
                return false;
            }

            path = arguments[1];
        }

        root = Path.GetFullPath(path);
        return true;
    }

    private static string RenderReceipt(
        string status,
        string worktree,
        string? donor,
        string method,
        string? pinSha256,
        string? reason,
        MathlibOleanInventory mathlibOleans,
        string? stampMiss,
        ClonefileReceipt? clonefile = null,
        LeanArchiveAttempt? archive = null) =>
        "LEAN_CACHE " + JsonSerializer.Serialize(new
        {
            status,
            worktree,
            donor,
            method,
            reason,
            stamp_miss = stampMiss,
            pin_sha256 = pinSha256,
            clonefile_errno = (clonefile ?? ClonefileReceipt.NotRun).LastErrno,
            clonefile_errnos = (clonefile ?? ClonefileReceipt.NotRun).Errnos,
            clonefile_attempts = (clonefile ?? ClonefileReceipt.NotRun).Attempts,
            clonefile_cleanup_error = (clonefile ?? ClonefileReceipt.NotRun).CleanupError,
            mathlib_missing_olean_files = mathlibOleans.MissingFiles,
            mathlib_missing_olean_samples = mathlibOleans.MissingSamples,
            // 归档这一路必须能从收据**唯一还原**发生了什么：试没试、什么结果、为什么。
            // 静默降级正是本战线一路删掉的那种设计（#2762 起）。
            archive_status = ArchiveStatus(archive),
            archive_mode = archive?.Mode,
            archive_skip_reason = archive?.SkipReason,
            archive_reason = archive?.Reason,
            archive_producer_commit_sha = archive?.ProducerCommitSha,
            archive_workflow_run_id = archive?.WorkflowRunId,
        }) + "\n";

    private static string ArchiveStatus(LeanArchiveAttempt? archive) =>
        (archive?.Outcome ?? LeanArchiveOutcome.NotAttempted) switch
        {
            LeanArchiveOutcome.Unpacked => "unpacked",
            LeanArchiveOutcome.Miss => "miss",
            LeanArchiveOutcome.Rejected => "rejected",
            LeanArchiveOutcome.Failed => "failed",
            _ => "not_attempted",
        };
}
