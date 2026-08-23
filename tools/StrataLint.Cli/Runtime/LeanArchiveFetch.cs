using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

/// <summary>
/// 内容层的私有供给。依赖层有 `lake exe cache get` 这个公共供给，内容层没有 —— 本仓那
/// 1408 个 olean 只有本仓有，无 donor 时它们此前只能从源码重编（#2729）。
///
/// 这里调的是 `lean-cache-publish.sh fetch`，它在解包前核验八类产地并对任一不符
/// fail-closed（#2844）。本类型只负责**把它的判词读回来**，不自行判断可信与否：
/// 归档是否可用由那个脚本判，这里判的只是「它说了什么」。
/// </summary>
internal enum LeanArchiveOutcome
{
    NotAttempted,
    Unpacked,
    Miss,
    Rejected,
    Failed,
}

internal sealed record LeanArchiveAttempt(
    LeanArchiveOutcome Outcome,
    string? Mode,
    string? ProducerCommitSha,
    string? WorkflowRunId,
    string? Reason,
    string? SkipReason)
{
    internal static LeanArchiveAttempt Skipped(string skipReason) =>
        new(LeanArchiveOutcome.NotAttempted, null, null, null, null, skipReason);
}

internal static class LeanArchiveFetch
{
    private const string ReceiptPrefix = "LEAN_CACHE_FETCH ";

    internal static string ScriptPath(string worktreeRoot) => Path.Combine(
        worktreeRoot,
        "tools",
        "scripts",
        "worktree",
        "lean-cache-publish.sh");

    internal static LeanArchiveAttempt Run(
        string worktreeRoot,
        IWorktreeProcessRunner runner,
        TimeSpan budget)
    {
        var script = ScriptPath(worktreeRoot);
        if (!File.Exists(script))
        {
            return new LeanArchiveAttempt(
                LeanArchiveOutcome.Failed,
                null,
                null,
                null,
                $"archive fetcher is absent: {script}",
                null);
        }

        ProcessOutput output;
        try
        {
            output = runner.Run(
                "/bin/bash",
                [script, "fetch", "--repository", worktreeRoot],
                worktreeRoot,
                budget);
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException
            or InvalidOperationException
            or TimeoutException)
        {
            // 网络与外部工具的失败在这里都是**可降级**的：内容层拿不到就退回重编，
            // 这是慢，不是错。真正不可降级的是产地不符 —— 那由脚本判 rejected。
            return new LeanArchiveAttempt(
                LeanArchiveOutcome.Failed,
                null,
                null,
                null,
                $"archive fetch did not run: {exception.Message}",
                null);
        }

        return Parse(output);
    }

    private static LeanArchiveAttempt Parse(ProcessOutput output)
    {
        var text = Encoding.UTF8.GetString(output.StandardOutput)
            + Encoding.UTF8.GetString(output.StandardError);
        var line = text
            .Split('\n')
            .LastOrDefault(static candidate =>
                candidate.TrimStart().StartsWith(ReceiptPrefix, StringComparison.Ordinal));
        if (line is null)
        {
            // 退出码本身不够：脚本可能因别的原因非零而没留判词。没有判词就是没有判词，
            // 不能按退出码猜它是 miss 还是 rejected。
            return new LeanArchiveAttempt(
                LeanArchiveOutcome.Failed,
                null,
                null,
                null,
                $"archive fetcher emitted no receipt (exit {output.ExitCode})",
                null);
        }

        try
        {
            using var document = JsonDocument.Parse(
                line.TrimStart()[ReceiptPrefix.Length..]);
            var root = document.RootElement;
            var status = Text(root, "status");
            var outcome = status switch
            {
                "unpacked" => LeanArchiveOutcome.Unpacked,
                "miss" => LeanArchiveOutcome.Miss,
                "rejected" => LeanArchiveOutcome.Rejected,
                _ => LeanArchiveOutcome.Failed,
            };
            var reason = Text(root, "reason");
            if (outcome == LeanArchiveOutcome.Rejected)
            {
                var stage = Text(root, "stage");
                reason = stage is null ? reason : $"{stage}: {reason}";
            }

            return new LeanArchiveAttempt(
                outcome,
                Text(root, "mode"),
                Text(root, "producer_commit_sha"),
                Text(root, "workflow_run_id"),
                outcome == LeanArchiveOutcome.Unpacked ? null : reason ?? status,
                null);
        }
        catch (JsonException exception)
        {
            return new LeanArchiveAttempt(
                LeanArchiveOutcome.Failed,
                null,
                null,
                null,
                $"archive receipt is malformed: {exception.Message}",
                null);
        }
    }

    private static string? Text(JsonElement element, string name) =>
        element.TryGetProperty(name, out var value) && value.ValueKind == JsonValueKind.String
            ? value.GetString()
            : null;
}
