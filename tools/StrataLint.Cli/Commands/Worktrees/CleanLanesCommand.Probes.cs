using StrataLint.Runtime;
using System.Globalization;
using System.Security.Cryptography;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private sealed record LockedLaneObservation(
        bool Eligible,
        string Reason,
        string? ContentFingerprint,
        string? HistoryFingerprint,
        string? EvidenceFingerprint,
        string? ActivityFingerprint,
        string? LockFingerprint)
    {
        internal static LockedLaneObservation Retained(string reason) =>
            new(false, reason, null, null, null, null, null);
    }

    private enum ContentProbeResult
    {
        Verified,
        Changed,
        Unknown,
    }

    private static readonly UTF8Encoding StrictContentUtf8 = new(false, true);

    private static LockedLaneObservation ProbeLockedLane(
        string repositoryRoot,
        RegisteredWorktree item,
        string baseCommit,
        string commonGitDirectory,
        IWorktreeProcessRunner runner,
        DateTimeOffset now,
        IReadOnlySet<string> activePaths,
        Func<IReadOnlySet<string>?> readHostActivity)
    {
        if (item.LockReason is null or { Length: 0 })
            return LockedLaneObservation.Retained("locked_unknown");

        if (!IsInitializationLock(item.LockReason))
        {
            return item.LockReason.StartsWith("worktree-init:", StringComparison.Ordinal)
                ? LockedLaneObservation.Retained("locked_unknown")
                : LockedLaneObservation.Retained("locked_intentional");
        }

        var hostActivity = HostActivityBlockReason(item, activePaths, readHostActivity);
        if (hostActivity is not null)
            return LockedLaneObservation.Retained(hostActivity);

        var evidence = TryReadInitializationEvidence(item, commonGitDirectory);
        if (evidence is null)
            return LockedLaneObservation.Retained("locked_evidence");

        var inactivity = ReclaimBlockReason(item, baseCommit, runner, now);
        if (inactivity is not null)
        {
            return LockedLaneObservation.Retained(inactivity switch
            {
                "recently_updated" or "age_unverifiable" => "locked_activity",
                "not_far_behind" => "locked_not_obsolete",
                _ => "locked_evidence",
            });
        }

        var activity = TryReadIndexLockActivity(item.GitDirectory!, now, out var active);
        if (activity is null)
            return LockedLaneObservation.Retained("locked_evidence");
        if (active)
            return LockedLaneObservation.Retained("locked_activity");

        var contentResult = TryReadHeadContentFingerprint(item, runner, out var content);
        if (contentResult == ContentProbeResult.Unknown)
            return LockedLaneObservation.Retained("locked_evidence");
        if (contentResult == ContentProbeResult.Changed)
            return LockedLaneObservation.Retained("locked_content");

        var history = TryReadHistoryFingerprint(item.GitDirectory!);
        if (history is null)
            return LockedLaneObservation.Retained("locked_evidence");
        var retainedHistory = ProbeRetainedHistory(repositoryRoot, item, baseCommit, runner);
        if (retainedHistory != ContentProbeResult.Verified)
            return LockedLaneObservation.Retained(retainedHistory == ContentProbeResult.Changed
                ? "locked_history" : "locked_evidence");

        return new LockedLaneObservation(
            true,
            "stale_initialization_lock",
            content,
            history,
            evidence,
            activity,
            FileState(Path.Combine(item.GitDirectory!, "locked")));
    }

    private static bool IsInitializationLock(string reason) =>
        reason.StartsWith("worktree-init:", StringComparison.Ordinal)
        && reason.Length == "worktree-init:".Length + 32
        && reason["worktree-init:".Length..].All(static character =>
            character is >= '0' and <= '9'
                or >= 'a' and <= 'f');

    private static string? TryReadInitializationEvidence(
        RegisteredWorktree item,
        string commonGitDirectory)
    {
        if (item.GitDirectory is null || !Directory.Exists(item.GitDirectory)) return null;
        try
        {
            var pointerPath = Path.Combine(item.Path, ".git");
            if (!File.Exists(pointerPath)) return null;
            var pointer = ReadSingleLine(pointerPath);
            const string prefix = "gitdir: ";
            if (pointer is null || !pointer.StartsWith(prefix, StringComparison.Ordinal)) return null;
            var pointedDirectory = Path.GetFullPath(pointer[prefix.Length..], item.Path);
            if (!PathsEqual(pointedDirectory, item.GitDirectory)) return null;

            var locked = ReadSingleLine(Path.Combine(item.GitDirectory, "locked"));
            var commondir = ReadSingleLine(Path.Combine(item.GitDirectory, "commondir"));
            var metadataHead = ReadSingleLine(Path.Combine(item.GitDirectory, "HEAD"));
            if ((item.Locked
                    ? !string.Equals(locked, item.LockReason, StringComparison.Ordinal)
                    : File.Exists(Path.Combine(item.GitDirectory, "locked")))
                || Directory.Exists(Path.Combine(item.GitDirectory, "locked"))
                || commondir is null
                || metadataHead is null)
                return null;

            var resolvedCommon = Path.GetFullPath(commondir, item.GitDirectory);
            if (!PathsEqual(resolvedCommon, commonGitDirectory)) return null;
            if (item.Branch is not null
                && !string.Equals(metadataHead, $"ref: refs/heads/{item.Branch}", StringComparison.Ordinal))
                return null;

            var state = new StringBuilder();
            foreach (var name in new[] { "gitdir", "commondir", "HEAD", "index" })
            {
                var path = Path.Combine(item.GitDirectory, name);
                state.Append(name).Append('=').Append(FileState(path)).Append('\n');
            }

            return Convert.ToHexString(SHA256.HashData(StrictContentUtf8.GetBytes(state.ToString())));
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static string? TryReadIndexLockActivity(
        string gitDirectory,
        DateTimeOffset now,
        out bool active)
    {
        active = false;
        try
        {
            var path = Path.Combine(gitDirectory, "index.lock");
            if (Directory.Exists(path)) return null;
            if (!File.Exists(path)) return "missing";
            var info = new FileInfo(path);
            var timestamp = info.LastWriteTimeUtc;
            var nowUtc = now.UtcDateTime;
            active = info.Length != 0
                || timestamp > nowUtc
                || nowUtc - timestamp < TimeSpan.FromSeconds(MinimumReclaimableLaneAgeSeconds);
            return $"{info.Length}:{timestamp.Ticks}";
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static string? TryReadHistoryFingerprint(string gitDirectory)
    {
        try
        {
            var path = Path.Combine(gitDirectory, "logs", "HEAD");
            return File.Exists(path)
                ? Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path)))
                : null;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static ContentProbeResult TryReadHeadContentFingerprint(
        RegisteredWorktree item,
        IWorktreeProcessRunner runner,
        out string? fingerprint)
    {
        fingerprint = null;
        try
        {
            var format = Decode(RunGit(
                item.Path,
                ["rev-parse", "--show-object-format"],
                runner,
                "could not read Git object format").StandardOutput).Trim();
            var tree = Decode(RunGit(
                item.Path,
                ["ls-tree", "-r", "-z", "--full-tree", item.Head],
                runner,
                "could not enumerate HEAD content").StandardOutput);
            var expected = new Dictionary<string, ExpectedContent>(StringComparer.Ordinal);
            foreach (var record in tree.Split('\0', StringSplitOptions.RemoveEmptyEntries))
            {
                var tab = record.IndexOf('\t');
                if (tab < 0) return ContentProbeResult.Unknown;
                var prefix = record[..tab];
                var fields = prefix.Split(' ', StringSplitOptions.RemoveEmptyEntries);
                if (fields.Length != 3) return ContentProbeResult.Unknown;
                var mode = fields[0];
                var objectId = fields[2];
                var path = record[(tab + 1)..];
                if (path.Length == 0 || !IsSupportedHeadMode(mode)) return ContentProbeResult.Unknown;
                expected.Add(path, new ExpectedContent(mode, objectId));
            }

            var actual = ReadWorktreeContent(item.Path);
            var indexPath = Path.Combine(item.GitDirectory!, "index");
            if (Directory.Exists(indexPath)) return ContentProbeResult.Unknown;
            var indexPresent = File.Exists(indexPath);
            if (indexPresent)
            {
                var staged = Decode(RunGit(item.Path, ["ls-files", "--stage", "-z"], runner,
                    "could not read staged content").StandardOutput);
                var indexedPaths = new HashSet<string>(StringComparer.Ordinal);
                foreach (var record in staged.Split('\0', StringSplitOptions.RemoveEmptyEntries))
                {
                    var tab = record.IndexOf('\t');
                    if (tab < 0) return ContentProbeResult.Unknown;
                    var fields = record[..tab].Split(' ', StringSplitOptions.RemoveEmptyEntries);
                    if (fields.Length != 3) return ContentProbeResult.Unknown;
                    var path = record[(tab + 1)..];
                    if (fields[2] != "0" || !indexedPaths.Add(path)
                        || !expected.TryGetValue(path, out var entry)
                        || fields[0] != entry.Mode || fields[1] != entry.ObjectId)
                        return ContentProbeResult.Changed;
                }
                if (indexedPaths.Count != expected.Count) return ContentProbeResult.Changed;
            }
            if (actual is null || (indexPresent && actual.Count != expected.Count)
                || actual.Keys.Any(path => !expected.ContainsKey(path)))
                return ContentProbeResult.Changed;

            foreach (var (path, entry) in actual)
            {
                var expectedEntry = expected[path];
                if (!string.Equals(entry.Mode, expectedEntry.Mode, StringComparison.Ordinal))
                    return ContentProbeResult.Changed;
                var bytes = entry.Mode == "120000"
                    ? StrictContentUtf8.GetBytes(entry.LinkTarget!)
                    : File.ReadAllBytes(Path.Combine(item.Path, path.Replace('/', Path.DirectorySeparatorChar)));
                var actualObject = ComputeGitBlobObjectId(bytes, format);
                if (!string.Equals(actualObject, expectedEntry.ObjectId, StringComparison.OrdinalIgnoreCase))
                    return ContentProbeResult.Changed;
            }

            var digest = SHA256.Create();
            foreach (var path in actual.Keys.Order(StringComparer.Ordinal))
            {
                var entry = expected[path];
                var line = $"{path}\0{entry.Mode}\0{entry.ObjectId}\0";
                var bytes = StrictContentUtf8.GetBytes(line);
                digest.TransformBlock(bytes, 0, bytes.Length, null, 0);
            }
            digest.TransformFinalBlock([], 0, 0);
            fingerprint = Convert.ToHexString(digest.Hash!);
            return ContentProbeResult.Verified;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return ContentProbeResult.Unknown;
        }
    }

    private sealed record ExpectedContent(string Mode, string ObjectId);

    private sealed record ActualContent(string Mode, string? LinkTarget);

    private static bool IsSupportedHeadMode(string mode) =>
        mode is "100644" or "100755" or "120000";

    private static Dictionary<string, ActualContent>? ReadWorktreeContent(string root)
    {
        try
        {
            var result = new Dictionary<string, ActualContent>(StringComparer.Ordinal);
            var pending = new Stack<(string FullPath, string RelativePath)>();
            foreach (var entry in Directory.EnumerateFileSystemEntries(root))
            {
                if (string.Equals(Path.GetFileName(entry), ".git", StringComparison.Ordinal)) continue;
                pending.Push((entry, Path.GetFileName(entry)));
            }

            while (pending.TryPop(out var current))
            {
                var info = new FileInfo(current.FullPath);
                var attributes = info.Attributes;
                if ((attributes & FileAttributes.ReparsePoint) != 0)
                {
                    if (info.LinkTarget is null) return null;
                    result.Add(current.RelativePath.Replace(Path.DirectorySeparatorChar, '/'),
                        new ActualContent("120000", info.LinkTarget));
                    continue;
                }

                if ((attributes & FileAttributes.Directory) != 0)
                {
                    foreach (var entry in Directory.EnumerateFileSystemEntries(current.FullPath))
                    {
                        pending.Push((entry, current.RelativePath + "/" + Path.GetFileName(entry)));
                    }
                    continue;
                }

                result.Add(current.RelativePath.Replace(Path.DirectorySeparatorChar, '/'),
                    new ActualContent(IsExecutable(info) ? "100755" : "100644", null));
            }

            return result;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return null;
        }
    }

    private static bool IsExecutable(FileInfo info) =>
        !OperatingSystem.IsWindows()
        && (info.UnixFileMode & (UnixFileMode.UserExecute
            | UnixFileMode.GroupExecute
            | UnixFileMode.OtherExecute)) != 0;

    private static string ComputeGitBlobObjectId(byte[] bytes, string objectFormat)
    {
        var header = StrictContentUtf8.GetBytes($"blob {bytes.Length}\0");
        using HashAlgorithm hash = objectFormat == "sha256" ? SHA256.Create() : SHA1.Create();
        hash.TransformBlock(header, 0, header.Length, null, 0);
        hash.TransformFinalBlock(bytes, 0, bytes.Length);
        return Convert.ToHexString(hash.Hash!).ToLowerInvariant();
    }

    private static string? ReadSingleLine(string path)
    {
        if (!File.Exists(path)) return null;
        var value = File.ReadAllText(path, StrictContentUtf8).TrimEnd('\r', '\n');
        return value.Length == 0 || value.AsSpan().IndexOfAny('\r', '\n') >= 0 ? null : value;
    }

    private static string FileState(string path)
    {
        if (Directory.Exists(path)) return "directory";
        if (!File.Exists(path)) return "missing";
        var info = new FileInfo(path);
        return $"{info.Length}:{info.LastWriteTimeUtc.Ticks}:"
            + Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(path)));
    }

    private static bool PathsEqual(string left, string right) =>
        string.Equals(
            Path.TrimEndingDirectorySeparator(CanonicalPath(left)),
            Path.TrimEndingDirectorySeparator(CanonicalPath(right)),
            OperatingSystem.IsWindows() ? StringComparison.OrdinalIgnoreCase : StringComparison.Ordinal);

    private static string CanonicalPath(string path)
    {
        var full = Path.GetFullPath(path);
        try
        {
            return Directory.Exists(full)
                ? ResolveDirectoryPath(full)
                : full;
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return full;
        }
    }

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
