using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private enum QualificationOutcome { Eligible, Refused, Failed, Deferred }

    private sealed record QualificationResult(string? Reason = null,
        QualificationOutcome Outcome = QualificationOutcome.Eligible, string? Diagnostic = null)
    {
        public bool Failed => Outcome is QualificationOutcome.Failed or QualificationOutcome.Deferred;
    }

    private static IReadOnlyDictionary<string, QualificationResult> QualifyLockedLanes(
        string root, IReadOnlyList<RegisteredWorktree> candidates, IWorktreeProcessRunner runner)
    {
        if (candidates.Count == 0) return new Dictionary<string, QualificationResult>();
        var paths = candidates.Select(item => item.Path).ToHashSet(StringComparer.Ordinal);
        var results = new Dictionary<string, QualificationResult>(StringComparer.Ordinal);
        var started = new HashSet<string>(StringComparer.Ordinal);
        var anyStarted = false;
        var snapshotFailed = false;
        var summarySeen = false;
        Exception? receiptError = null;
        CommandResult? result = null;
        IReadOnlyDictionary<string, QualificationResult> InvalidBatch(Exception exception)
        {
            var failure = QualificationFailure(exception, result);
            failure = failure with { Reason = "qualification_failed:batch_protocol_error:" + failure.Reason };
            return paths.ToDictionary(path => path, path => results.TryGetValue(path, out var prior) && prior.Failed
                ? prior with { Diagnostic = failure.Reason } : failure, StringComparer.Ordinal);
        }
        try
        {
            var budget = Math.Min(600L * paths.Count, 3600L);
            var arguments = new List<string> { "qualify", "--stream", "--budget-seconds",
                budget.ToString(System.Globalization.CultureInfo.InvariantCulture) };
            foreach (var path in paths) arguments.AddRange(["--path", path]);
            result = WorktreeProtocolCommand.RunLines(root, arguments, runner, TimeSpan.FromSeconds(budget), line =>
            {
                if (receiptError is not null) return;
                try
                {
                    using var document = JsonDocument.Parse(line);
                    var row = document.RootElement;
                    if (summarySeen) throw new InvalidOperationException("rows after qualification summary");
                    if (row.GetProperty("event").GetString() == "worktree_qualification_started")
                    {
                        var activePath = row.GetProperty("path").GetString()!;
                        if (!paths.Contains(activePath) || results.ContainsKey(activePath) || started.Count != 0 || snapshotFailed)
                            throw new InvalidOperationException("invalid qualification start");
                        started.Add(activePath);
                        anyStarted = true;
                        return;
                    }
                    if (row.GetProperty("event").GetString() == "worktree_qualification")
                    {
                        var failed = results.Values.Any(item => item.Failed);
                        if (row.GetProperty("item_count").GetInt32() != paths.Count || results.Count != paths.Count || started.Count != 0
                            || row.GetProperty("status").GetString() != (failed ? "failed" : "succeeded"))
                            throw new InvalidOperationException("incomplete or inconsistent qualification receipt");
                        summarySeen = true;
                        return;
                    }
                    if (row.GetProperty("event").GetString() != "worktree_qualification_item")
                        throw new InvalidOperationException("unexpected qualification event");
                    var path = row.GetProperty("path").GetString()!;
                    var outcome = row.GetProperty("outcome").GetString();
                    var reason = row.GetProperty("reason").GetString();
                    if (!paths.Contains(path) || results.ContainsKey(path)
                        || outcome == "qualified" && reason is not null
                        || outcome is "refused" or "failed" or "deferred" && string.IsNullOrWhiteSpace(reason)
                        || outcome is "failed" or "deferred" && !reason!.StartsWith("qualification_failed:", StringComparison.Ordinal)
                        || outcome is not ("qualified" or "refused" or "failed" or "deferred"))
                        throw new InvalidOperationException("invalid or duplicate qualification item");
                    var snapshotFailure = outcome == "failed" && !anyStarted;
                    if (outcome == "deferred" ? started.Count != 0
                        : snapshotFailure ? started.Count != 0 : !started.Contains(path))
                        throw new InvalidOperationException("unpaired qualification item");
                    snapshotFailed |= snapshotFailure;
                    started.Remove(path);
                    results.Add(path, new QualificationResult(reason, outcome switch
                    {
                        "qualified" => QualificationOutcome.Eligible,
                        "refused" => QualificationOutcome.Refused,
                        "failed" => QualificationOutcome.Failed,
                        _ => QualificationOutcome.Deferred,
                    }));
                }
                catch (Exception error) when (error is not OutOfMemoryException)
                {
                    receiptError = new InvalidOperationException("invalid qualification row:" + BoundedDiagnostic(line), error);
                }
            });
            if (receiptError is not null) throw receiptError;
            if (!summarySeen || result.Error.Length != 0
                || result.ExitCode != (results.Values.Any(item => item.Failed) ? 74 : 0))
                throw new InvalidOperationException("missing summary or inconsistent qualification exit");
            return results;
        }
        catch (TimeoutException exception)
        {
            // RunStreaming drains its callback before returning/throwing.
            // Completed observations survive; no receipt grants removal authority.
            if (receiptError is not null)
                return InvalidBatch(receiptError);
            var failure = QualificationFailure(exception, result);
            if (results.Count == paths.Count && !results.Values.Any(item => item.Failed))
                results.Add(string.Empty, failure);
            foreach (var path in paths)
                results.TryAdd(path, started.Contains(path) ? failure : failure with
                    { Reason = "qualification_failed:deferred:" + failure.Reason, Outcome = QualificationOutcome.Deferred });
            return results;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return InvalidBatch(exception);
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
            if (refusal is not null) return new(refusal, QualificationOutcome.Refused);
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

    internal static string? CanonicalRefusal(CommandResult result)
    {
        const string prefix = "WORKTREE_RETAINED ";
        var error = result.Error.TrimEnd('\r', '\n');
        return result.ExitCode is 68 or 73 && result.Output.Length == 0
            && error.StartsWith(prefix, StringComparison.Ordinal) && error.Length > prefix.Length
            && !error.Contains('\n') && !error.Contains('\r') ? error[prefix.Length..] : null;
    }

    private static QualificationResult QualificationFailure(Exception exception, CommandResult? result)
    {
        const string prefix = "WORKTREE_FAILED ";
        if (result?.ExitCode == 74 && result.Output.Length == 0 && result.Error.StartsWith(prefix, StringComparison.Ordinal))
            return new(BoundedDiagnostic(result.Error[prefix.Length..].TrimEnd('\r', '\n')), QualificationOutcome.Failed);
        var diagnostic = exception.GetType().Name + ":" + BoundedDiagnostic(exception.Message);
        return new("qualification_failed:" + (result is not null
            ? "protocol_error:exit=" + result.ExitCode + ":stderr=" + BoundedDiagnostic(result.Error)
                + ":stdout=" + BoundedDiagnostic(result.Output) + ":" + diagnostic
            : (exception is TimeoutException ? "timeout:" : "unavailable:") + diagnostic), QualificationOutcome.Failed);
    }

    internal static string BoundedDiagnostic(string value) => value.Length <= 4096 ? value
        : value[..2048] + "...[truncated]..." + value[^2048..];

    private static CleanLaneEvent QualificationEvent(RegisteredWorktree item, QualificationResult result) =>
        BlockedWorktree(item, result.Reason!) with
            { Action = result.Failed ? "failed" : "skipped", Diagnostic = result.Diagnostic };
}
