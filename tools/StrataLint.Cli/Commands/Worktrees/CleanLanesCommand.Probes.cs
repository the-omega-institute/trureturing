using System.Globalization;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    internal static string? TryResolveRegisteredGitDirectory(
        string path,
        IWorktreeProcessRunner runner)
    {
        if (!Directory.Exists(path) || !HasGitMarker(path)) return null;
        try
        {
            return TryResolveGitDirectory(path, runner);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static bool IsAncestor(
        string repositoryRoot,
        string ancestor,
        string descendant,
        IWorktreeProcessRunner runner)
    {
        var result = runner.Run(
            "git",
            ["merge-base", "--is-ancestor", ancestor, descendant],
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode == 0) return true;
        if (result.ExitCode == 1) return false;
        var error = Decode(result.StandardError).Trim();
        throw new InvalidOperationException(
            error.Length == 0 ? "could not compare lane ancestry" : error);
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

    private static string? ReclaimBlockReason(
        RegisteredWorktree item,
        string baseCommit,
        IWorktreeProcessRunner runner,
        DateTimeOffset now)
    {
        var updated = ReadLastUpdate(item.GitDirectory!, item.Head);
        if (updated is null) return "update_unknown";
        try
        {
            var commitTime = Decode(RunGit(
                item.Path, ["show", "-s", "--format=%ct", item.Head], runner,
                "could not read HEAD commit time").StandardOutput).Trim();
            if (!long.TryParse(commitTime, NumberStyles.None, CultureInfo.InvariantCulture,
                    out var committed)) return "update_unknown";
            updated = Math.Max(updated.Value, committed);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "update_unknown";
        }

        var nowSeconds = now.ToUnixTimeSeconds();
        if (updated > nowSeconds) return "age_unverifiable";
        if (nowSeconds - updated < MinimumReclaimableLaneAgeSeconds) return "recently_updated";
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

    // Trust Git's local clock; source file mtimes and uncommitted changes are irrelevant.
    private static long? ReadLastUpdate(string gitDirectory, string observedHead)
    {
        try
        {
            long? latest = null;
            string? lastHead = null;
            foreach (var line in File.ReadLines(Path.Combine(gitDirectory, "logs", "HEAD"), StrictUtf8))
            {
                var tab = line.IndexOf('\t');
                var record = tab < 0 ? line : line[..tab];
                var fields = record.Split(' ', StringSplitOptions.RemoveEmptyEntries);
                if (fields.Length < 6 || !IsObjectOid(fields[0]) || !IsObjectOid(fields[1])
                    || !long.TryParse(fields[^2], NumberStyles.None, CultureInfo.InvariantCulture,
                        out var timestamp) || !IsTimezone(fields[^1])) return null;
                latest = Math.Max(latest ?? timestamp, timestamp);
                lastHead = fields[1];
            }

            return string.Equals(lastHead, observedHead, StringComparison.Ordinal) ? latest : null;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static bool IsObjectOid(string? value) =>
        value is not null
        && value.Length is 40 or 64
        && value.All(static character =>
            character is >= '0' and <= '9'
                or >= 'a' and <= 'f'
                or >= 'A' and <= 'F');

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
