using StrataLint.Runtime;
using System.Globalization;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    internal static (string? GitDirectory, string? Failure) ObserveRegisteredGitDirectory(
        string path,
        IWorktreeProcessRunner runner)
    {
        if (!Directory.Exists(path) || !HasGitMarker(path)) return (null, null);
        try
        {
            var directory = Decode(RunGit(path, ["rev-parse", "--absolute-git-dir"], runner,
                "could not read worktree Git directory").StandardOutput).Trim();
            if (directory.Length == 0) throw new InvalidOperationException("empty worktree Git directory");
            return (directory, null);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return (null, Directory.Exists(path) && HasGitMarker(path) ? IdentityFailure(exception) : null);
        }
    }

    private static string IdentityFailure(Exception exception) =>
        "qualification_failed:identity:" + (exception is TimeoutException ? "timeout:" : "")
        + exception.GetType().Name + ":" + BoundedDiagnostic(exception.Message);

    private static bool? IsAncestor(
        string repositoryRoot,
        string ancestor,
        string descendant,
        IWorktreeProcessRunner runner)
    {
        try
        {
            var result = runner.Run(
                "git",
                ["merge-base", "--is-ancestor", ancestor, descendant],
                repositoryRoot,
                BoundedProcessRunner.HangDetectionBudget);
            return result.ExitCode switch { 0 => true, 1 => false, _ => null };
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    internal static ProcessOutput RunGit(
        string workingDirectory,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        string fallback)
    {
        var result = runner.Run("git", arguments, workingDirectory, TimeSpan.FromSeconds(120));
        if (result.ExitCode == 0) return result;
        var error = Decode(result.StandardError).Trim();
        throw new InvalidOperationException(error.Length == 0 ? fallback : error);
    }

    internal static string Decode(byte[] bytes) => StrictUtf8.GetString(bytes);

    private static long? ReadLastUpdate(
        RegisteredWorktree item, IWorktreeProcessRunner runner)
    {
        try
        {
            var commitTime = Decode(RunGit(
                item.Path, ["show", "-s", "--format=%ct", item.Head], runner,
                "could not read HEAD commit time").StandardOutput).Trim();
            if (!long.TryParse(commitTime, NumberStyles.None, CultureInfo.InvariantCulture,
                    out var committed)) return null;
            return committed;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static string? UpdateAgeBlockReason(long updated, long minimumAge, DateTimeOffset now)
    {
        var nowSeconds = now.ToUnixTimeSeconds();
        if (updated > nowSeconds) return "age_unverifiable";
        return nowSeconds - updated < minimumAge ? "recently_updated" : null;
    }

    private static string? OriginalReclaimBlockReason(
        RegisteredWorktree item, string baseCommit, long updated,
        IWorktreeProcessRunner runner, DateTimeOffset now)
    {
        var reason = UpdateAgeBlockReason(updated, MinimumReclaimableLaneAgeSeconds, now);
        if (reason is not null) return reason;
        try
        {
            var output = Decode(RunGit(
                item.Path, ["rev-list", "--count", $"{item.Head}..{baseCommit}"], runner,
                "could not count commits behind base").StandardOutput).Trim();
            if (!long.TryParse(output, NumberStyles.None, CultureInfo.InvariantCulture,
                    out var behind)) return "behind_unknown";
            return behind < MinimumBehindCommits ? "not_far_behind" : null;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "behind_unknown";
        }
    }

    private static bool IsObjectOid(string? value) =>
        value is not null
        && value.Length is 40 or 64
        && value.All(static character =>
            character is >= '0' and <= '9'
                or >= 'a' and <= 'f'
                or >= 'A' and <= 'F');

    private static bool TryParseHeadLogRecord(string line, out HeadLogRecord? record)
    {
        // The message separator follows the complete identity, timestamp and
        // timezone; a committer name can itself contain a TAB.
        var match = Regex.Match(line,
            @"^(?<old>[0-9a-fA-F]+) (?<new>[0-9a-fA-F]+) (?<name>[^<>]+) <[^<>]*> (?<time>[0-9]+) (?<zone>[+-][0-9]{4})(?:\t(?<message>.*))?$",
            RegexOptions.CultureInvariant);
        var oldHead = match.Groups["old"].Value;
        var newHead = match.Groups["new"].Value;
        record = null;
        if (!match.Success || !IsObjectOid(oldHead) || !IsObjectOid(newHead)
            || oldHead.Length != newHead.Length
            || string.IsNullOrWhiteSpace(match.Groups["name"].Value)
            || !long.TryParse(match.Groups["time"].Value, NumberStyles.None,
                CultureInfo.InvariantCulture, out var timestamp)
            || !IsTimezone(match.Groups["zone"].Value)) return false;
        record = new(oldHead, newHead, timestamp, match.Groups["message"].Value);
        return true;
    }

    private sealed record HeadLogRecord(string OldHead, string NewHead, long Updated, string Message);

    private static bool IsTimezone(string value) =>
        value.Length == 5
        && value[0] is '+' or '-'
        && int.TryParse(
            value.AsSpan(1, 2),
            NumberStyles.None,
            CultureInfo.InvariantCulture,
            out var hours)
        && int.TryParse(
            value.AsSpan(3, 2),
            NumberStyles.None,
            CultureInfo.InvariantCulture,
            out var minutes)
        && hours <= 23
        && minutes <= 59;

}
