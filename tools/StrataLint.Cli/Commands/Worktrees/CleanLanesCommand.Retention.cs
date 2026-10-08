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
        string commonDirectory,
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
            // Only the files ref backend has the recovery surfaces checked below.
            if (Decode(RunGit(item.Path, ["rev-parse", "--show-ref-format"], runner,
                    "could not inspect ref storage").StandardOutput).Trim() != "files")
                return ContentProbeResult.Unknown;
            if (!TryReadRecoveryHistory(item, commonDirectory, out _, out var commits))
                return ContentProbeResult.Unknown;
            if (!commits.All(commit => IsAncestor(item.Path, commit, baseCommit, runner)))
                return ContentProbeResult.Changed;
            var messagePath = Path.Combine(item.GitDirectory!, "COMMIT_EDITMSG");
            if (File.Exists(messagePath))
            {
                var commit = Decode(RunGit(item.Path, ["cat-file", "commit", item.Head], runner,
                    "could not verify retained commit message").StandardOutput);
                var separator = commit.IndexOf("\n\n", StringComparison.Ordinal);
                if (separator < 0 || File.ReadAllText(messagePath, StrictUtf8) != commit[(separator + 2)..])
                    return ContentProbeResult.Unknown;
            }
            return ContentProbeResult.Verified;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return ContentProbeResult.Unknown;
        }
    }

    // These are the recovery handles destroyed by private administration removal
    // and managed branch deletion. Unrecognized operation state is retained.
    private static bool TryReadRecoveryHistory(
        RegisteredWorktree item,
        string commonDirectory,
        out string? fingerprint,
        out HashSet<string> commits)
    {
        fingerprint = null;
        commits = new(StringComparer.Ordinal) { item.Head };
        try
        {
            var logs = new List<string>();
            var refs = new List<string>();
            var state = new System.Text.StringBuilder();
            void ReadTree(string directory, List<string> files)
            {
                foreach (var entry in Directory.EnumerateFileSystemEntries(directory).Order(StringComparer.Ordinal))
                {
                    if ((File.GetAttributes(entry) & FileAttributes.ReparsePoint) != 0)
                        throw new IOException("unverifiable private recovery link");
                    state.Append(entry).Append('\n');
                    if (Directory.Exists(entry)) ReadTree(entry, files);
                    else files.Add(entry);
                }
            }
            foreach (var entry in Directory.EnumerateFileSystemEntries(item.GitDirectory!).Order(StringComparer.Ordinal))
            {
                if ((File.GetAttributes(entry) & FileAttributes.ReparsePoint) != 0) return false;
                var name = Path.GetFileName(entry);
                if (name is "logs" or "refs" && Directory.Exists(entry))
                    ReadTree(entry, name == "logs" ? logs : refs);
                else if (!File.Exists(entry)) return false;
                else if (name is "gitdir" or "commondir" or "HEAD" or "index" or "index.lock" or "locked")
                    continue;
                else if (name == "COMMIT_EDITMSG")
                    state.Append(entry).Append('=').Append(FileState(entry)).Append('\n');
                else if (name.All(character => character is >= 'A' and <= 'Z' or '_'))
                    refs.Add(entry);
                else return false;
            }
            if (!logs.Contains(Path.Combine(item.GitDirectory!, "logs", "HEAD"), StringComparer.Ordinal))
                return false;
            if (RetiringBranchLog(item, commonDirectory) is { } branchLog)
            {
                if (Directory.Exists(branchLog)) return false;
                state.Append(branchLog).Append('=').Append(FileState(branchLog)).Append('\n');
                if (File.Exists(branchLog)) logs.Add(branchLog);
            }
            foreach (var reference in refs)
            {
                state.Append(reference).Append('=').Append(FileState(reference)).Append('\n');
                var lines = File.ReadAllLines(reference, StrictUtf8);
                if (lines.Length == 0 || lines.Any(line => !IsObjectOid(line))) return false;
                foreach (var commit in lines)
                    if (commit.Any(character => character != '0')) commits.Add(commit);
            }
            foreach (var log in logs)
            {
                state.Append(log).Append('=').Append(FileState(log)).Append('\n');
                foreach (var line in File.ReadLines(log, StrictUtf8))
                {
                    var tab = line.IndexOf('\t');
                    var fields = (tab < 0 ? line : line[..tab]).Split(' ', StringSplitOptions.RemoveEmptyEntries);
                    if (fields.Length < 6 || !IsObjectOid(fields[0]) || !IsObjectOid(fields[1])) return false;
                    foreach (var commit in fields.Take(2))
                        if (commit.Any(character => character != '0')) commits.Add(commit);
                }
            }
            fingerprint = Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(
                StrictContentUtf8.GetBytes(state.ToString())));
            return true;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return false;
        }
    }

    private static string? RetiringBranchLog(RegisteredWorktree item, string commonDirectory) =>
        item.Branch is not null && WorktreeCommand.IsManagedBranch(item.Branch)
            ? Path.Combine(commonDirectory, "logs", "refs", "heads", item.Branch)
            : null;
}
