using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private sealed record QualificationResult(string? Reason = null, bool Failed = false);

    private static IReadOnlyDictionary<string, QualificationResult> QualifyLockedLanes(
        string root, IReadOnlyList<RegisteredWorktree> candidates, IWorktreeProcessRunner runner)
    {
        if (candidates.Count == 0) return new Dictionary<string, QualificationResult>();
        var paths = candidates.Select(item => item.Path).ToHashSet(StringComparer.Ordinal);
        CommandResult? result = null;
        try
        {
            var arguments = new List<string> { "qualify" };
            foreach (var path in paths) arguments.AddRange(["--path", path]);
            result = WorktreeProtocolCommand.Run(root, arguments, runner, TimeSpan.FromSeconds(600));
            if (result.ExitCode is not (0 or 74) || result.Error.Length != 0)
                throw new InvalidOperationException("unexpected qualification exit or stderr");
            using var document = JsonDocument.Parse(result.Output);
            var receipt = document.RootElement;
            if (receipt.GetProperty("event").GetString() != "worktree_qualification")
                throw new InvalidOperationException("unexpected qualification event");
            var results = new Dictionary<string, QualificationResult>(StringComparer.Ordinal);
            foreach (var row in receipt.GetProperty("items").EnumerateArray())
            {
                var path = row.GetProperty("path").GetString()!;
                var outcome = row.GetProperty("outcome").GetString();
                var reason = row.GetProperty("reason").GetString();
                if (!paths.Contains(path) || results.ContainsKey(path)
                    || outcome == "qualified" && reason is not null
                    || outcome is "refused" or "failed" && string.IsNullOrWhiteSpace(reason)
                    || outcome == "failed" && !reason!.StartsWith("qualification_failed:", StringComparison.Ordinal)
                    || outcome is not ("qualified" or "refused" or "failed"))
                    throw new InvalidOperationException("invalid qualification item");
                results.Add(path, new QualificationResult(reason, outcome == "failed"));
            }
            var failed = results.Values.Any(item => item.Failed);
            if (results.Count != paths.Count || result.ExitCode != (failed ? 74 : 0)
                || receipt.GetProperty("status").GetString() != (failed ? "failed" : "succeeded"))
                throw new InvalidOperationException("incomplete or inconsistent qualification receipt");
            return results;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            var failure = QualificationFailure(exception, result);
            return paths.ToDictionary(path => path, _ => failure, StringComparer.Ordinal);
        }
    }

    private static QualificationResult PreviewLane(
        string root, RegisteredWorktree item, IWorktreeProcessRunner runner)
    {
        CommandResult? result = null;
        try
        {
            result = WorktreeProtocolCommand.Run(root,
                ["remove", "--path", item.Path, "--preview"], runner, TimeSpan.FromSeconds(600));
            var refusal = CanonicalRefusal(result);
            if (refusal is not null) return new(refusal);
            if (!result.Success || result.Error.Length != 0)
                throw new InvalidOperationException("unexpected preview exit or stderr");
            using var document = JsonDocument.Parse(result.Output);
            var receipt = document.RootElement;
            var row = receipt.GetProperty("items").EnumerateArray().Single();
            if (receipt.GetProperty("event").GetString() != "worktree_removal"
                || receipt.GetProperty("status").GetString() != "succeeded"
                || row.GetProperty("path").GetString() != item.Path
                || row.GetProperty("outcome").GetString() != "would_remove")
                throw new InvalidOperationException("invalid preview receipt");
            return new();
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return QualificationFailure(exception, result);
        }
    }

    private static string? CanonicalRefusal(CommandResult result)
    {
        const string prefix = "WORKTREE_RETAINED ";
        var error = result.Error.TrimEnd('\r', '\n');
        return result.ExitCode is 68 or 73 && result.Output.Length == 0
            && error.StartsWith(prefix, StringComparison.Ordinal) && error.Length > prefix.Length
            && !error.Contains('\n') && !error.Contains('\r') ? error[prefix.Length..] : null;
    }

    private static QualificationResult QualificationFailure(Exception exception, CommandResult? result)
    {
        var diagnostic = exception.GetType().Name + ":" + exception.Message;
        return new("qualification_failed:" + (result is not null
            ? "protocol_error:exit=" + result.ExitCode + ":stderr=" + FirstLine(result.Error)
                + ":stdout=" + FirstLine(result.Output) + ":" + diagnostic
            : (exception is TimeoutException ? "timeout:" : "unavailable:") + diagnostic), Failed: true);
    }

    private static string FirstLine(string value) => value.Split(['\r', '\n'], 2)[0];

    private static CleanLaneEvent QualificationEvent(RegisteredWorktree item, QualificationResult result) =>
        BlockedWorktree(item, result.Reason!) with { Action = result.Failed ? "failed" : "skipped" };
}
