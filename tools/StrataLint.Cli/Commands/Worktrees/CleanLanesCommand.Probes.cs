using System.Globalization;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class CleanLanesCommand
{
    private static string? TryResolveRegisteredGitDirectory(
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

    private static ProcessOutput RunGit(
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

    private static string Decode(byte[] bytes) => StrictUtf8.GetString(bytes);

    private static CreationRecord ReadCreationRecord(string gitDirectory)
    {
        try
        {
            var path = Path.Combine(gitDirectory, "logs", "HEAD");
            if (!File.Exists(path)) return default;
            var line = File.ReadLines(path, StrictUtf8).FirstOrDefault();
            if (string.IsNullOrEmpty(line)) return default;
            var tab = line.IndexOf('\t');
            // `tab == 0` 才是畸形(记录部分为空)。**行末制表符只是空 reflog message**,
            // 而 message 根本不参与下面的解析 —— `record` 只取制表符**之前**的部分。
            // 把它当畸形会让整棵 lane 被判 `creation_unknown` 而永远无法回收(#3459)。
            // 实测本机 127 棵有 `logs/HEAD` 的 worktree:**114 棵**(89.8%)首行的制表符在行末。
            if (tab == 0) return default;
            var record = tab < 0 ? line : line[..tab];
            var fields = record.Split(' ', StringSplitOptions.RemoveEmptyEntries);
            if (fields.Length < 6
                || !IsZeroObjectOid(fields[0])
                || !IsObjectOid(fields[1])
                || !long.TryParse(
                    fields[^2],
                    NumberStyles.None,
                    CultureInfo.InvariantCulture,
                    out var timestamp)
                || !IsTimezone(fields[^1]))
            {
                return default;
            }

            return new CreationRecord(
                true,
                fields[1],
                DateTimeOffset.FromUnixTimeSeconds(timestamp));
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return default;
        }
    }

    private static PullRequestProbeOutcome ProbePullRequests(
        string repositoryRoot,
        string branch,
        IWorktreeProcessRunner runner)
    {
        try
        {
            var result = runner.Run(
                "gh",
                [
                    "pr",
                    "list",
                    "--state",
                    "all",
                    "--head",
                    branch,
                    "--json",
                    "state,headRefName,headRefOid,mergeCommit",
                    "--limit",
                    "100",
                ],
                repositoryRoot,
                BoundedProcessRunner.HangDetectionBudget);
            if (result.ExitCode != 0
                || result.StandardOutput.Length == 0
                || result.StandardError.Length != 0)
            {
                return new PullRequestProbeOutcome(false, []);
            }

            using var document = JsonDocument.Parse(result.StandardOutput);
            if (document.RootElement.ValueKind != JsonValueKind.Array)
            {
                return new PullRequestProbeOutcome(false, []);
            }

            var pullRequests = new List<PullRequestInfo>();
            foreach (var item in document.RootElement.EnumerateArray())
            {
                if (item.ValueKind != JsonValueKind.Object
                    || !item.TryGetProperty("headRefName", out var headBranchElement)
                    || headBranchElement.ValueKind != JsonValueKind.String
                    || string.IsNullOrEmpty(headBranchElement.GetString())
                    || !item.TryGetProperty("headRefOid", out var headOidElement)
                    || headOidElement.ValueKind != JsonValueKind.String
                    || !IsObjectOid(headOidElement.GetString())
                    || !item.TryGetProperty("state", out var stateElement)
                    || stateElement.ValueKind != JsonValueKind.String
                    || stateElement.GetString() is not ("OPEN" or "CLOSED" or "MERGED")
                    || !item.TryGetProperty("mergeCommit", out var mergeCommitElement))
                {
                    return new PullRequestProbeOutcome(false, []);
                }

                string? mergeCommitOid = null;
                if (mergeCommitElement.ValueKind == JsonValueKind.Object)
                {
                    if (!mergeCommitElement.TryGetProperty("oid", out var oidElement)
                        || oidElement.ValueKind != JsonValueKind.String
                        || !IsObjectOid(oidElement.GetString()))
                    {
                        return new PullRequestProbeOutcome(false, []);
                    }

                    mergeCommitOid = oidElement.GetString();
                }
                else if (mergeCommitElement.ValueKind != JsonValueKind.Null)
                {
                    return new PullRequestProbeOutcome(false, []);
                }

                var state = stateElement.GetString()!;
                if (state == "MERGED" && mergeCommitOid is null)
                {
                    return new PullRequestProbeOutcome(false, []);
                }

                pullRequests.Add(new PullRequestInfo(
                    headBranchElement.GetString()!,
                    headOidElement.GetString()!,
                    state,
                    mergeCommitOid));
            }

            return new PullRequestProbeOutcome(true, pullRequests);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new PullRequestProbeOutcome(false, []);
        }
    }

    private static LaneProcessProbeOutcome ProbeLaneProcesses(
        string canonicalLanePath,
        IWorktreeProcessRunner runner)
    {
        try
        {
            var result = runner.Run(
                "lsof",
                ["-nP", "-F0pfn"],
                Path.GetTempPath(),
                BoundedProcessRunner.HangDetectionBudget);
            if (result.ExitCode != 0
                || result.StandardOutput.Length == 0
                || result.StandardError.Length != 0
                || !TryParseLsofSnapshot(
                    result.StandardOutput,
                    canonicalLanePath,
                    out var inUse))
            {
                return new LaneProcessProbeOutcome(false, false);
            }

            return new LaneProcessProbeOutcome(true, inUse);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new LaneProcessProbeOutcome(false, false);
        }
    }

    private static bool TryParseLsofSnapshot(
        byte[] bytes,
        string canonicalLanePath,
        out bool inUse)
    {
        inUse = false;
        var processSeen = false;
        var fileSeen = false;
        var nameSeen = true;
        var index = 0;
        while (index < bytes.Length)
        {
            if (bytes[index] == (byte)'\n') index++;
            if (index >= bytes.Length) break;
            var end = Array.IndexOf(bytes, (byte)0, index);
            if (end <= index) return false;
            var field = StrictUtf8.GetString(bytes, index, end - index);
            index = end + 1;
            switch (field[0])
            {
                case 'p':
                    if (field.Length == 1
                        || field.AsSpan(1).ContainsAnyExceptInRange('0', '9')
                        || !nameSeen
                        || (processSeen && !fileSeen))
                    {
                        return false;
                    }

                    processSeen = true;
                    fileSeen = false;
                    break;
                case 'f':
                    if (!processSeen || field.Length == 1 || !nameSeen) return false;
                    fileSeen = true;
                    nameSeen = false;
                    break;
                case 'n':
                    if (!processSeen || !fileSeen || nameSeen || field.Length == 1) return false;
                    nameSeen = true;
                    var observedPath = field[1..];
                    if (Path.IsPathRooted(observedPath))
                    {
                        observedPath = CanonicalPath(observedPath);
                        if (string.Equals(
                                observedPath,
                                canonicalLanePath,
                                StringComparison.Ordinal)
                            || observedPath.StartsWith(
                                canonicalLanePath + Path.DirectorySeparatorChar,
                                StringComparison.Ordinal))
                        {
                            inUse = true;
                        }
                    }

                    break;
                default:
                    return false;
            }
        }

        return processSeen && fileSeen && nameSeen;
    }

    private static bool PullRequestIsWellFormed(PullRequestInfo pullRequest) =>
        !string.IsNullOrEmpty(pullRequest.HeadBranch)
        && IsObjectOid(pullRequest.HeadOid)
        && pullRequest.State is "OPEN" or "CLOSED" or "MERGED"
        && (pullRequest.MergeCommitOid is null || IsObjectOid(pullRequest.MergeCommitOid))
        && (pullRequest.State != "MERGED" || pullRequest.MergeCommitOid is not null);

    private static bool IsZeroObjectOid(string value) =>
        value.Length is 40 or 64 && value.All(static character => character == '0');

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

    private static string CanonicalPath(string path) =>
        Path.TrimEndingDirectorySeparator(Path.GetFullPath(path));

    private readonly record struct CreationRecord(
        bool Valid,
        string InitialHead,
        DateTimeOffset Timestamp);
}
