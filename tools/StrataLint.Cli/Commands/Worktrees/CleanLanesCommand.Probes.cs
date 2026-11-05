using StrataLint.Runtime;
using System.Globalization;
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

    private static string? UpdateAgeBlockReason(long updated, DateTimeOffset now)
    {
        var nowSeconds = now.ToUnixTimeSeconds();
        if (updated > nowSeconds) return "age_unverifiable";
        return nowSeconds - updated < MinimumReclaimableLaneAgeSeconds ? "recently_updated" : null;
    }

    private static bool IsObjectOid(string? value) =>
        value is not null
        && value.Length is 40 or 64
        && value.All(static character =>
            character is >= '0' and <= '9'
                or >= 'a' and <= 'f'
                or >= 'A' and <= 'F');

}
