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
            // 这是慢，不是错。
            //
            // 产地不符（脚本判 rejected）是**不可消费**，不是不可降级 —— 那份归档一个
            // 字节都不能用，但调用方仍可降级到从可信源码重编。安全门与可用性策略是
            // 两件事，别混：门决定「能不能吃」，策略决定「吃不上怎么办」。
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
            if (root.ValueKind != JsonValueKind.Object)
            {
                // 语法合法但结构不对的判词照样得降级。`[]` 是合法 JSON，而在数组上
                // 取属性抛的是 InvalidOperationException 而非 JsonException（实测），
                // 只接后者会让异常逃出本 helper、把整个 ensure 打挂 —— 那正是本类型
                // 声称要避免的「失败可降级」的反面。
                return new LeanArchiveAttempt(
                    LeanArchiveOutcome.Failed,
                    null,
                    null,
                    null,
                    $"archive receipt is not an object ({root.ValueKind})",
                    null);
            }

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

            // 判词与退出码必须自洽。脚本的约定是 unpacked → 0、miss/rejected → 非零；
            // 两者矛盾时说明判词与实际发生的事对不上，此时**不采信判词**，判 Failed。
            // 这不是不信退出码，也不是只信退出码 —— 是要求两个独立信号一致。
            var consistent = outcome switch
            {
                LeanArchiveOutcome.Unpacked => output.ExitCode == 0,
                LeanArchiveOutcome.Miss or LeanArchiveOutcome.Rejected => output.ExitCode != 0,
                _ => true,
            };
            if (!consistent)
            {
                return new LeanArchiveAttempt(
                    LeanArchiveOutcome.Failed,
                    null,
                    null,
                    null,
                    $"archive receipt says {status} but the fetcher exited {output.ExitCode}",
                    null);
            }

            return new LeanArchiveAttempt(
                outcome,
                Text(root, "mode"),
                Text(root, "producer_commit_sha"),
                Text(root, "workflow_run_id"),
                outcome == LeanArchiveOutcome.Unpacked ? null : reason ?? status,
                null);
        }
        catch (Exception exception) when (exception is JsonException
            or InvalidOperationException)
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
