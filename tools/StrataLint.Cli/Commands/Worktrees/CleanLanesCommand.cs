using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record CleanLanesOptions(string Base, bool Force, bool LanesOnly);

internal sealed record PullRequestInfo(
    string HeadBranch,
    string HeadOid,
    string State,
    string? MergeCommitOid);

internal sealed record PullRequestProbeOutcome(
    bool Success,
    IReadOnlyList<PullRequestInfo> PullRequests);

internal sealed record LaneProcessProbeOutcome(bool Success, bool InUse);

internal delegate PullRequestProbeOutcome PullRequestProbe(
    string repositoryRoot,
    string branch,
    IWorktreeProcessRunner runner);

internal delegate LaneProcessProbeOutcome LaneProcessProbe(
    string canonicalLanePath,
    IWorktreeProcessRunner runner);

internal static partial class CleanLanesCommand
{
    internal const string Usage =
        "USAGE: StrataLint clean-lanes [--base REV] [--force] [--lanes-only]";

    private const long MinimumReclaimableLaneAgeSeconds = 24L * 60 * 60; // #2769 safety grace bound.

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        DateTimeOffset now) =>
        Run(
            repositoryRoot,
            arguments,
            new ProductionWorktreeProcessRunner(),
            DefaultTempRoots(),
            now);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IReadOnlyList<string> tempRoots,
        DateTimeOffset now) =>
        Run(
            repositoryRoot,
            arguments,
            runner,
            tempRoots,
            now,
            ProbePullRequests,
            ProbeLaneProcesses);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IReadOnlyList<string> tempRoots,
        DateTimeOffset now,
        PullRequestProbe pullRequestProbe,
        LaneProcessProbe laneProcessProbe)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(tempRoots);
        ArgumentNullException.ThrowIfNull(pullRequestProbe);
        ArgumentNullException.ThrowIfNull(laneProcessProbe);
        try
        {
            var root = Path.GetFullPath(repositoryRoot);
            var options = ParseArguments(arguments);
            var baseCommit = ResolveCommit(root, options.Base, runner);
            var commonGitDirectory = ResolveCommonGitDirectory(root, runner);
            var currentGitDirectory = ResolveGitDirectory(root, runner);
            var inventory = ReadWorktrees(root, runner);
            var events = new List<CleanLaneEvent>();
            var activeBranches = inventory
                .Where(static item => item.Branch is not null)
                .Select(static item => item.Branch!)
                .ToHashSet(StringComparer.Ordinal);

            InspectRegisteredLanes(
                root,
                currentGitDirectory,
                baseCommit,
                options.Force,
                inventory,
                events,
                runner,
                now,
                pullRequestProbe,
                laneProcessProbe);
            if (!options.LanesOnly)
            {
                // 建树时的回收够不到这两类:判官树的判据(未注册 / 无 .git 的快照)
                // 区分不了「跑完了」和「正在跑」,而建树常发生在派席前后;孤儿分支
                // 不占一棵树,删它是纯分支操作,不属于「顺手回收旧树」。
                InspectOrphanBranches(
                    root,
                    baseCommit,
                    options.Force,
                    activeBranches,
                    events,
                    runner);
                InspectTempJudges(
                    root,
                    commonGitDirectory,
                    options.Force,
                    inventory,
                    tempRoots,
                    events,
                    runner);
            }

            var partialCount = events.Count(static item => item.Action == "partially_removed");
            var output = new StringBuilder();
            foreach (var item in events
                .OrderBy(static item => item.Kind, StringComparer.Ordinal)
                .ThenBy(static item => item.Path, StringComparer.Ordinal)
                .ThenBy(static item => item.Branch, StringComparer.Ordinal))
            {
                output.Append(JsonSerializer.Serialize(new
                {
                    @event = "clean_lanes_item",
                    kind = item.Kind,
                    path = item.Path,
                    branch = item.Branch,
                    head = item.Head,
                    action = item.Action,
                    reason = item.Reason,
                }));
                output.Append('\n');
            }

            output.Append(JsonSerializer.Serialize(new
            {
                @event = "clean_lanes_summary",
                mode = options.Force ? "force" : "dry_run",
                scope = options.LanesOnly ? "lanes_only" : "full",
                base_revision = options.Base,
                base_commit = baseCommit,
                item_count = events.Count,
                removable_count = events.Count(static item =>
                    item.Action is "would_remove" or "removed"),
                removed_count = events.Count(static item => item.Action == "removed"),
                partial_count = partialCount,
            }));
            output.Append('\n');
            return new CommandResult(
                partialCount == 0,
                output.ToString(),
                partialCount == 0
                    ? string.Empty
                    : $"CLEAN_LANES_PARTIAL_FAILURE count={partialCount}\n");
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"CLEAN_LANES_FAILED {exception.Message}\n");
        }
    }

    internal static CleanLanesOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        var baseRevision = "origin/dev";
        var baseSeen = false;
        var force = false;
        var lanesOnly = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--force" when !force:
                    force = true;
                    break;
                case "--lanes-only" when !lanesOnly:
                    lanesOnly = true;
                    break;
                case "--base" when !baseSeen:
                    if (++index >= arguments.Count || arguments[index].Length == 0)
                    {
                        throw new InvalidOperationException(Usage);
                    }

                    baseRevision = arguments[index];
                    baseSeen = true;
                    break;
                default:
                    throw new InvalidOperationException(Usage);
            }
        }

        return new CleanLanesOptions(baseRevision, force, lanesOnly);
    }

    private static void InspectRegisteredLanes(
        string repositoryRoot,
        string currentGitDirectory,
        string baseCommit,
        bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        ICollection<CleanLaneEvent> events,
        IWorktreeProcessRunner runner,
        DateTimeOffset now,
        PullRequestProbe pullRequestProbe,
        LaneProcessProbe laneProcessProbe)
    {
        foreach (var item in inventory.Where(static item =>
            item.Branch is not null && WorktreeCommand.IsManagedBranch(item.Branch)))
        {
            if (string.Equals(item.Path, repositoryRoot, StringComparison.Ordinal)
                || string.Equals(item.GitDirectory, currentGitDirectory, StringComparison.Ordinal))
            {
                events.Add(BlockedWorktree(item, "current"));
                continue;
            }

            if (!Directory.Exists(item.Path))
            {
                events.Add(BlockedWorktree(item, "missing"));
                continue;
            }

            if (!HasGitMarker(item.Path))
            {
                events.Add(BlockedWorktree(item, "unreadable"));
                continue;
            }

            if (item.GitDirectory is null)
            {
                events.Add(BlockedWorktree(item, "unreadable"));
                continue;
            }

            if (item.Locked)
            {
                events.Add(BlockedWorktree(item, "locked"));
                continue;
            }

            ProcessOutput status;
            try
            {
                status = RunGit(
                    item.Path,
                    ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
                    runner,
                    "could not inspect worktree status");
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                events.Add(BlockedWorktree(item, "unreadable"));
                continue;
            }

            if (status.StandardOutput.Length != 0)
            {
                events.Add(BlockedWorktree(item, "dirty"));
                continue;
            }

            var creation = ReadCreationRecord(item.GitDirectory);
            if (!creation.Valid)
            {
                events.Add(BlockedWorktree(item, "creation_unknown"));
                continue;
            }

            // The age term trusts the local Git clock and the worktree's own creation reflog.
            var creationSeconds = creation.Timestamp.ToUnixTimeSeconds();
            var nowSeconds = now.ToUnixTimeSeconds();
            if (creationSeconds > nowSeconds)
            {
                events.Add(BlockedWorktree(item, "age_unverifiable"));
                continue;
            }

            if (nowSeconds - creationSeconds < MinimumReclaimableLaneAgeSeconds)
            {
                events.Add(BlockedWorktree(item, "too_young"));
                continue;
            }

            if (string.Equals(item.Head, creation.InitialHead, StringComparison.Ordinal))
            {
                events.Add(BlockedWorktree(item, "never_worked"));
                continue;
            }

            {
                PullRequestProbeOutcome probe;
                try
                {
                    probe = pullRequestProbe(repositoryRoot, item.Branch!, runner);
                }
                catch (Exception exception) when (exception is not OutOfMemoryException)
                {
                    events.Add(BlockedWorktree(item, "pr_unknown"));
                    continue;
                }

                if (!probe.Success || probe.PullRequests is null)
                {
                    events.Add(BlockedWorktree(item, "pr_unknown"));
                    continue;
                }

                var authorized = false;
                var malformed = false;
                try
                {
                    foreach (var pullRequest in probe.PullRequests)
                    {
                        if (!PullRequestIsWellFormed(pullRequest))
                        {
                            malformed = true;
                            break;
                        }

                        if (pullRequest.State == "MERGED"
                            && string.Equals(
                                pullRequest.HeadBranch,
                                item.Branch,
                                StringComparison.Ordinal)
                            && string.Equals(
                                pullRequest.HeadOid,
                                item.Head,
                                StringComparison.Ordinal)
                            && IsAncestor(
                                repositoryRoot,
                                pullRequest.MergeCommitOid!,
                                baseCommit,
                                runner))
                        {
                            authorized = true;
                            break;
                        }
                    }
                }
                catch (Exception exception) when (exception is not OutOfMemoryException)
                {
                    events.Add(BlockedWorktree(item, "pr_unknown"));
                    continue;
                }

                if (malformed)
                {
                    events.Add(BlockedWorktree(item, "pr_unknown"));
                    continue;
                }

                if (!authorized)
                {
                    events.Add(BlockedWorktree(item, "pr_not_merged"));
                    continue;
                }
            }

            {
                LaneProcessProbeOutcome probe;
                try
                {
                    probe = laneProcessProbe(CanonicalPath(item.Path), runner);
                }
                catch (Exception exception) when (exception is not OutOfMemoryException)
                {
                    events.Add(BlockedWorktree(item, "in_use_unknown"));
                    continue;
                }

                if (!probe.Success)
                {
                    events.Add(BlockedWorktree(item, "in_use_unknown"));
                    continue;
                }

                if (probe.InUse)
                {
                    events.Add(BlockedWorktree(item, "in_use"));
                    continue;
                }
            }

            if (force)
            {
                events.Add(RemovalEvent(item, RemoveLane(
                    repositoryRoot,
                    item,
                    runner,
                    laneProcessProbe)));
                continue;
            }

            events.Add(new CleanLaneEvent(
                "merged_worktree",
                item.Path,
                item.Branch,
                item.Head,
                "would_remove",
                "merged_clean"));
        }
    }

    private static void InspectOrphanBranches(
        string repositoryRoot,
        string baseCommit,
        bool force,
        IReadOnlySet<string> activeBranches,
        ICollection<CleanLaneEvent> events,
        IWorktreeProcessRunner runner)
    {
        var branchOutput = RunGit(
            repositoryRoot,
            [
                "for-each-ref",
                "--format=%(refname:short)",
                "refs/heads",
            ],
            runner,
            "could not enumerate managed branches");
        var branches = Decode(branchOutput.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries)
            .Where(WorktreeCommand.IsManagedBranch)
            .Where(branch => !activeBranches.Contains(branch))
            .Order(StringComparer.Ordinal);
        foreach (var branch in branches)
        {
            var head = ResolveCommit(repositoryRoot, $"refs/heads/{branch}", runner);
            if (!IsAncestor(repositoryRoot, head, baseCommit, runner))
            {
                events.Add(new CleanLaneEvent(
                    "orphan_branch",
                    null,
                    branch,
                    head,
                    "skipped",
                    "unmerged"));
                continue;
            }

            if (force)
            {
                DeleteObservedRef(repositoryRoot, branch, head, runner);
            }

            events.Add(new CleanLaneEvent(
                "orphan_branch",
                null,
                branch,
                head,
                force ? "removed" : "would_remove",
                "merged_without_worktree"));
        }
    }

    private static void InspectTempJudges(
        string repositoryRoot,
        string commonGitDirectory,
        bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        IReadOnlyList<string> tempRoots,
        ICollection<CleanLaneEvent> events,
        IWorktreeProcessRunner runner)
    {
        var registeredByGitDirectory = inventory
            .Where(static item => item.GitDirectory is not null)
            .ToDictionary(
                static item => item.GitDirectory!,
                static item => item,
                StringComparer.Ordinal);
        foreach (var path in tempRoots
            .Where(Directory.Exists)
            .SelectMany(static root => Directory.EnumerateDirectories(
                root,
                "trureturing-*",
                SearchOption.TopDirectoryOnly))
            .Select(Path.GetFullPath)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal))
        {
            if ((File.GetAttributes(path) & FileAttributes.ReparsePoint) != 0)
            {
                events.Add(new CleanLaneEvent(
                    "temp_judge",
                    path,
                    null,
                    null,
                    "skipped",
                    "symlink"));
                continue;
            }

            var scannedGitDirectory = TryResolveGitDirectory(path, runner);
            if (scannedGitDirectory is not null
                && registeredByGitDirectory.TryGetValue(scannedGitDirectory, out var registered))
            {
                if (registered.Branch is not null)
                {
                    events.Add(new CleanLaneEvent(
                        "temp_judge",
                        path,
                        registered.Branch,
                        registered.Head,
                        "skipped",
                        "attached_branch"));
                    continue;
                }

                if (force)
                {
                    RunGit(
                        repositoryRoot,
                        ["worktree", "remove", "--force", path],
                        runner,
                        "could not remove detached judge worktree");
                }

                events.Add(new CleanLaneEvent(
                    "temp_judge",
                    path,
                    null,
                    registered.Head,
                    force ? "removed" : "would_remove",
                    "detached_same_repository"));
                continue;
            }

            if (!HasSameRepositoryPointer(path, commonGitDirectory))
            {
                if (!File.Exists(Path.Combine(path, ".git"))
                    && !Directory.Exists(Path.Combine(path, ".git"))
                    && HasGitlessJudgeShape(path))
                {
                    if (force)
                    {
                        if (!HasGitlessJudgeShape(path))
                        {
                            throw new InvalidOperationException(
                                $"judge snapshot identity changed during cleanup: {path}");
                        }

                        Directory.Delete(path, recursive: true);
                    }

                    events.Add(new CleanLaneEvent(
                        "temp_judge",
                        path,
                        null,
                        null,
                        force ? "removed" : "would_remove",
                        "gitless_judge_snapshot"));
                    continue;
                }

                events.Add(new CleanLaneEvent(
                    "temp_judge",
                    path,
                    null,
                    null,
                    "skipped",
                    File.Exists(Path.Combine(path, ".git"))
                        || Directory.Exists(Path.Combine(path, ".git"))
                        ? "foreign_git_directory"
                        : "not_judge_tree"));
                continue;
            }

            if (force)
            {
                Directory.Delete(path, recursive: true);
            }

            events.Add(new CleanLaneEvent(
                "temp_judge",
                path,
                null,
                null,
                force ? "removed" : "would_remove",
                "unregistered_same_repository"));
        }
    }

    private static void DeleteObservedRef(
        string repositoryRoot,
        string branch,
        string observedHead,
        IWorktreeProcessRunner runner) =>
        RunGit(
            repositoryRoot,
            ["update-ref", "-d", $"refs/heads/{branch}", observedHead],
            runner,
            "managed branch moved during cleanup");

    private static bool HasSameRepositoryPointer(string path, string commonGitDirectory)
    {
        var pointerPath = Path.Combine(path, ".git");
        if (!File.Exists(pointerPath)) return false;
        var line = File.ReadLines(pointerPath, StrictUtf8).FirstOrDefault();
        const string prefix = "gitdir: ";
        if (line is null || !line.StartsWith(prefix, StringComparison.Ordinal)) return false;
        var raw = line[prefix.Length..];
        if (raw.Length == 0) return false;
        var gitDirectory = Path.IsPathRooted(raw)
            ? Path.GetFullPath(raw)
            : Path.GetFullPath(raw, path);
        var relative = Path.GetRelativePath(commonGitDirectory, gitDirectory);
        return !Path.IsPathRooted(relative)
            && !string.Equals(relative, "..", StringComparison.Ordinal)
            && !relative.StartsWith("../", StringComparison.Ordinal)
            && !relative.StartsWith("..\\", StringComparison.Ordinal);
    }

    private static bool HasGitlessJudgeShape(string path) =>
        File.Exists(Path.Combine(path, "CLAUDE.md"))
        && File.Exists(Path.Combine(path, "AGENTS.md"))
        && File.Exists(Path.Combine(path, "Trureturing.lean"))
        && File.Exists(Path.Combine(path, "lean-toolchain"))
        && Directory.Exists(Path.Combine(path, "D5"))
        && Directory.Exists(Path.Combine(path, "tools"))
        && File.Exists(Path.Combine(path, ".github", "scripts", "harness-gate.sh"));

    private static IReadOnlyList<RegisteredWorktree> ReadWorktrees(
        string repositoryRoot,
        IWorktreeProcessRunner runner)
    {
        var result = RunGit(
            repositoryRoot,
            ["worktree", "list", "--porcelain", "-z"],
            runner,
            "could not enumerate git worktrees");
        var entries = new List<RegisteredWorktree>();
        string? path = null;
        string? head = null;
        string? branch = null;
        var locked = false;
        foreach (var field in Decode(result.StandardOutput).Split('\0'))
        {
            if (field.StartsWith("worktree ", StringComparison.Ordinal))
            {
                path = Path.GetFullPath(field["worktree ".Length..]);
            }
            else if (field.StartsWith("HEAD ", StringComparison.Ordinal))
            {
                head = field["HEAD ".Length..];
            }
            else if (field.StartsWith("branch refs/heads/", StringComparison.Ordinal))
            {
                branch = field["branch refs/heads/".Length..];
            }
            else if (field == "locked" || field.StartsWith("locked ", StringComparison.Ordinal))
            {
                locked = true;
            }
            else if (field.Length == 0 && path is not null)
            {
                if (head is null)
                {
                    throw new InvalidOperationException($"worktree inventory omitted HEAD: {path}");
                }

                entries.Add(new RegisteredWorktree(
                    path,
                    head,
                    branch,
                    TryResolveRegisteredGitDirectory(path, runner),
                    locked));
                path = null;
                head = null;
                branch = null;
                locked = false;
            }
        }

        return entries;
    }

    private static string ResolveCommit(
        string repositoryRoot,
        string revision,
        IWorktreeProcessRunner runner) =>
        Decode(RunGit(
            repositoryRoot,
            ["rev-parse", "--verify", "--end-of-options", $"{revision}^{{commit}}"],
            runner,
            $"revision does not resolve: {revision}").StandardOutput).Trim();

    private static string ResolveCommonGitDirectory(
        string repositoryRoot,
        IWorktreeProcessRunner runner)
    {
        var value = Decode(RunGit(
            repositoryRoot,
            ["rev-parse", "--git-common-dir"],
            runner,
            "could not resolve common Git directory").StandardOutput).Trim();
        return Path.IsPathRooted(value)
            ? Path.GetFullPath(value)
            : Path.GetFullPath(value, repositoryRoot);
    }

    private static string ResolveGitDirectory(
        string repositoryRoot,
        IWorktreeProcessRunner runner) =>
        Decode(RunGit(
            repositoryRoot,
            ["rev-parse", "--absolute-git-dir"],
            runner,
            "could not resolve worktree Git directory").StandardOutput).Trim();

    private static string? TryResolveGitDirectory(
        string repositoryRoot,
        IWorktreeProcessRunner runner)
    {
        var result = runner.Run(
            "git",
            ["rev-parse", "--absolute-git-dir"],
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget);
        return result.ExitCode == 0
            ? Decode(result.StandardOutput).Trim()
            : null;
    }

    private static bool HasGitMarker(string path) =>
        File.Exists(Path.Combine(path, ".git"))
        || Directory.Exists(Path.Combine(path, ".git"));

    private static CleanLaneEvent BlockedWorktree(RegisteredWorktree item, string reason) =>
        new("lane_worktree", item.Path, item.Branch, item.Head, "skipped", reason);

    private static IReadOnlyList<string> DefaultTempRoots() =>
        new[] { "/tmp", Path.GetTempPath() }
            .Where(Directory.Exists)
            .Select(Path.GetFullPath)
            .Distinct(StringComparer.Ordinal)
            .ToArray();

    private sealed record RegisteredWorktree(
        string Path,
        string Head,
        string? Branch,
        string? GitDirectory,
        bool Locked);

    private sealed record CleanLaneEvent(
        string Kind,
        string? Path,
        string? Branch,
        string? Head,
        string Action,
        string Reason);
}
