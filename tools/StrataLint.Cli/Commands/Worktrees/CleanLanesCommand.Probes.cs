using StrataLint.Runtime;
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

    private static string? OriginalReclaimBlockReason(
        RegisteredWorktree item,
        string baseCommit,
        long updated,
        IWorktreeProcessRunner runner,
        DateTimeOffset now)
    {
        try
        {
            var commitTime = Decode(RunGit(
                item.Path, ["show", "-s", "--format=%ct", item.Head], runner,
                "could not read HEAD commit time").StandardOutput).Trim();
            if (!long.TryParse(commitTime, NumberStyles.None, CultureInfo.InvariantCulture,
                    out var committed)) return "update_unknown";
            updated = Math.Max(updated, committed);
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
