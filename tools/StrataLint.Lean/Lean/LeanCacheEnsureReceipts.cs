using System.Text.Json;
using System.Text.Json.Nodes;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

// ensure 的收据渲染。与状态机正交：状态机决定「发生了什么」，这里只决定「怎么写下来」。
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
        ClonefileReceipt? clonefile = null,
        LeanArchiveAttempt? archive = null) =>
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
                clonefile,
                archive));

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
        out string root,
        out string? donorRepository)
    {
        var path = repositoryRoot;
        var selectedPath = false;
        donorRepository = null;
        root = string.Empty;
        for (var index = 0; index < arguments.Count; index += 2)
        {
            if (index + 1 >= arguments.Count || string.IsNullOrWhiteSpace(arguments[index + 1])
                || arguments[index + 1] is "--path" or "--donor-repository" or "--") return false;
            switch (arguments[index])
            {
                case "--path" when !selectedPath:
                    path = arguments[index + 1];
                    selectedPath = true;
                    break;
                case "--donor-repository" when donorRepository is null:
                    donorRepository = Path.GetFullPath(arguments[index + 1]);
                    break;
                default: return false;
            }
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
    private static CommandResult LinkedLaneReseedFailure(
        string root,
        LeanPinSet pins,
        LeanWorktreeLocation location,
        string? stampMiss,
        ClonefileReceipt? clonefile = null,
        string? reason = null)
    {
        var lake = ShellQuote(LeanCacheGuard.PhysicalPath(Path.Combine(root, ".lake")));
        var remediation = "the lane's content layer is cold while the main checkout is warm: "
            + $"remove {lake} and re-run so ensure seeds it from the main checkout";
        return FailureReceipt(
            "failed",
            root,
            location.MainCheckout,
            "none",
            pins.Sha256,
            JoinReasons(reason, remediation) ?? remediation,
            stampMiss,
            clonefile,
            LeanArchiveAttempt.Skipped(LinkedArchiveDisabled));
    }

    private static CommandResult LinkedFailure(
        string root,
        LeanPinSet pins,
        LeanWorktreeLocation location,
        string? reason,
        string? stampMiss,
        ClonefileReceipt? clonefile = null)
    {
        var remediation = "sync dev and warm the dev cache: "
            + $"make -C {ShellQuote(location.MainCheckout)} warm-donor";
        var completeReason = reason?.Contains(remediation, StringComparison.Ordinal) == true
            ? reason
            : JoinReasons(reason, remediation) ?? remediation;
        return FailureReceipt(
            "failed",
            root,
            location.MainCheckout,
            "none",
            pins.Sha256,
            completeReason,
            stampMiss,
            clonefile,
            LeanArchiveAttempt.Skipped(LinkedArchiveDisabled));
    }

    private static string RecordColdBuildConsent(string receipt)
    {
        const string prefix = "LEAN_CACHE ";
        if (!receipt.StartsWith(prefix, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("Lean cache receipt has an unexpected prefix");
        }
        var payload = JsonNode.Parse(receipt[prefix.Length..]) as JsonObject
            ?? throw new InvalidOperationException("Lean cache receipt is not a JSON object");
        payload["cold_build_consent"] = true;
        return prefix + payload.ToJsonString() + "\n";
    }

    private static string RecordCacheState(string receipt, CacheState cacheState)
    {
        const string prefix = "LEAN_CACHE ";
        if (!receipt.StartsWith(prefix, StringComparison.Ordinal))
        {
            throw new InvalidOperationException("Lean cache receipt has an unexpected prefix");
        }
        var payload = JsonNode.Parse(receipt[prefix.Length..]) as JsonObject
            ?? throw new InvalidOperationException("Lean cache receipt is not a JSON object");
        payload["mathlib_olean_state"] = ReceiptWarmth(cacheState.Mathlib.State);
        payload["mathlib_olean_probe_error"] = cacheState.Mathlib.Error;
        payload["project_olean_state"] = ReceiptWarmth(cacheState.Project.State);
        payload["project_olean_probe_error"] = cacheState.Project.Error;
        return prefix + payload.ToJsonString() + "\n";
    }

    private static string ReceiptWarmth(OleanWarmth warmth) => warmth switch
    {
        OleanWarmth.Cold => "cold",
        OleanWarmth.Warm => "warm",
        OleanWarmth.ProbeFailed => "probe_failed",
        _ => throw new ArgumentOutOfRangeException(nameof(warmth), warmth, null),
    };

}
