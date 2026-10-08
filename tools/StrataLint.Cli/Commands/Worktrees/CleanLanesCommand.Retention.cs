using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static IReadOnlySet<string>? TryReadHostActivity(
        string repositoryRoot,
        IWorktreeProcessRunner runner)
    {
        try
        {
            var checkoutRoot = Decode(RunGit(repositoryRoot, ["rev-parse", "--show-toplevel"], runner,
                "could not locate host activity sampler").StandardOutput).Trim();
            var result = runner.Run("python3",
                ["-B", Path.Combine(checkoutRoot, "tools/scripts/host-cleanup.py"), "active-paths"],
                repositoryRoot, TimeSpan.FromSeconds(180));
            if (result.ExitCode != 0) return null;
            var paths = JsonSerializer.Deserialize<string[]>(Decode(result.StandardOutput));
            if (paths is null || paths.Any(path => !Path.IsPathFullyQualified(path))) return null;
            return paths.Select(CanonicalPath).ToHashSet(StringComparer.Ordinal);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static string? HostActivityBlockReason(
        RegisteredWorktree item,
        IReadOnlySet<string> explicitActivePaths,
        Func<IReadOnlySet<string>?> readHostActivity)
    {
        try
        {
            var observed = readHostActivity();
            if (observed is null) return "locked_activity_unknown";
            return observed.Concat(explicitActivePaths).Any(path =>
                IsWithin(item.Path, path) || (item.GitDirectory is not null && IsWithin(item.GitDirectory, path)))
                ? "locked_activity" : null;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return "locked_activity_unknown";
        }
    }

    private static bool IsWithin(string root, string path)
    {
        root = Path.TrimEndingDirectorySeparator(CanonicalPath(root));
        path = CanonicalPath(path);
        return string.Equals(root, path, StringComparison.Ordinal)
            || path.StartsWith(root + Path.DirectorySeparatorChar, StringComparison.Ordinal);
    }

    private static ContentProbeResult ProbeRetainedHistory(
        string repositoryRoot,
        RegisteredWorktree item,
        string baseCommit,
        IWorktreeProcessRunner runner)
    {
        try
        {
            var currentHead = ResolveCommit(repositoryRoot, "HEAD", runner);
            if (!IsAncestor(item.Path, baseCommit, currentHead, runner))
            {
                var refs = Decode(RunGit(item.Path,
                    ["for-each-ref", "--format=%(refname)", "--contains", baseCommit], runner,
                    "could not verify retained base").StandardOutput)
                    .Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
                if (!refs.Any(reference => reference.StartsWith("refs/remotes/", StringComparison.Ordinal)
                    || reference.StartsWith("refs/tags/", StringComparison.Ordinal)
                    || (reference.StartsWith("refs/heads/", StringComparison.Ordinal)
                        && !WorktreeCommand.IsManagedBranch(reference["refs/heads/".Length..]))))
                    return ContentProbeResult.Changed;
            }
            // BASE must retain both the current tip and every commit whose local HEAD
            // reflog would disappear with this worktree, including commits reset away.
            var commits = new HashSet<string>(StringComparer.Ordinal) { item.Head };
            foreach (var line in File.ReadLines(Path.Combine(item.GitDirectory!, "logs", "HEAD"), StrictUtf8))
            {
                var tab = line.IndexOf('\t');
                var fields = (tab < 0 ? line : line[..tab]).Split(' ', StringSplitOptions.RemoveEmptyEntries);
                if (fields.Length < 6 || !IsObjectOid(fields[0]) || !IsObjectOid(fields[1]))
                    return ContentProbeResult.Unknown;
                foreach (var commit in fields.Take(2))
                    if (commit.Any(character => character != '0')) commits.Add(commit);
            }
            return commits.All(commit => IsAncestor(item.Path, commit, baseCommit, runner))
                ? ContentProbeResult.Verified : ContentProbeResult.Changed;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return ContentProbeResult.Unknown;
        }
    }
}
