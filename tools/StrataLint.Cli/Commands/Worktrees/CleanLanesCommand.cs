using StrataLint.Runtime;
using static StrataLint.Cli.RegisteredWorktreeInventory;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record CleanLanesOptions(
    string Base,
    bool Force,
    bool LanesOnly,
    IReadOnlySet<string> ActivePaths);

internal static partial class CleanLanesCommand
{
    internal const string Usage =
        "USAGE: StrataLint clean-lanes [--base REV] [--force] [--lanes-only] "
        + "[--active-paths-file FILE]";

    private const long MinimumReclaimableLaneAgeSeconds = 24L * 60 * 60;
    private const long MinimumBehindCommits = 300;

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
        DateTimeOffset now)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(tempRoots);
        try
        {
            var root = Path.GetFullPath(repositoryRoot);
            var options = ParseArguments(arguments);
            var baseCommit = ResolveCommit(root, options.Base, runner);
            var commonGitDirectory = ResolveCommonGitDirectory(root, runner);
            var inventory = ReadWorktrees(root, runner);
            root = inventory[0].Path; // Keep Git commands usable when the invoking linked tree is selected.
            var events = new List<CleanLaneEvent>();
            var activeBranches = inventory
                .Where(static item => item.Branch is not null)
                .Select(static item => item.Branch!)
                .ToHashSet(StringComparer.Ordinal);
            var protectedInventory = inventory.ToList();
            void ProtectObservedWorktree(RegisteredWorktree observed)
            {
                if (observed.Branch is not null) activeBranches.Add(observed.Branch);
                protectedInventory.Add(observed);
            }

            var extraSweepsAllowed = InspectRegisteredLanes(
                root,
                commonGitDirectory,
                baseCommit,
                options.Force,
                inventory,
                events,
                runner,
                now,
                ProtectObservedWorktree);
            if (!options.LanesOnly && extraSweepsAllowed)
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
                    commonGitDirectory,
                    options.Force,
                    protectedInventory,
                    tempRoots,
                    events,
                    runner);
            }

            var failedCount = events.Count(static item => item.Action == "failed");
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
                extra_sweeps = options.LanesOnly ? "not_requested"
                    : extraSweepsAllowed ? "completed" : "deferred",
                extra_sweeps_reason = !options.LanesOnly && !extraSweepsAllowed
                    ? "lane_removal_unresolved" : null,
                base_revision = options.Base,
                base_commit = baseCommit,
                item_count = events.Count,
                removable_count = events.Count(static item =>
                    item.Action is "would_remove" or "removed"),
                removed_count = events.Count(static item => item.Action == "removed"),
                partial_count = partialCount,
                failed_count = failedCount,
            }));
            output.Append('\n');
            return new CommandResult(
                partialCount + failedCount == 0,
                output.ToString(),
                partialCount + failedCount == 0
                    ? string.Empty
                    : $"CLEAN_LANES_PARTIAL_FAILURE count={partialCount + failedCount}\n");
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
        var activePaths = new HashSet<string>(StringComparer.Ordinal);
        var activePathsSeen = false;
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
                case "--active-paths-file" when !activePathsSeen:
                    if (++index >= arguments.Count || arguments[index].Length == 0)
                    {
                        throw new InvalidOperationException(Usage);
                    }

                    // Accepted for older callers; activity never governs worktree deletion.
                    activePathsSeen = true;
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

        return new CleanLanesOptions(baseRevision, force, lanesOnly, activePaths);
    }

    private static bool InspectRegisteredLanes(
        string repositoryRoot,
        string commonGitDirectory,
        string baseCommit,
        bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        ICollection<CleanLaneEvent> events,
        IWorktreeProcessRunner runner,
        DateTimeOffset now,
        Action<RegisteredWorktree> protectObservedWorktree)
    {
        var remainingPaths = inventory.Select(static item => item.Path).ToHashSet(StringComparer.Ordinal);
        var retainedLocks = inventory.Where(static item => item.Locked)
            .Select(static item => item.Path).ToHashSet(StringComparer.Ordinal);
        var incomplete = false;
        void Observe(RegisteredWorktree observed)
        {
            protectObservedWorktree(observed);
            if (observed.Locked) retainedLocks.Add(observed.Path);
        }

        void CompleteRemoval(RegisteredWorktree item, LaneRemovalResult removal)
        {
            if (removal.Outcome == LaneRemovalOutcome.Removed)
            {
                remainingPaths.Remove(item.Path);
                retainedLocks.Remove(item.Path);
            }
            else incomplete = true;
        }

        foreach (var item in inventory.OrderByDescending(static item => item.Path.Length))
        {
            if (string.Equals(item.GitDirectory, commonGitDirectory, StringComparison.Ordinal))
            {
                events.Add(BlockedWorktree(item, "main_worktree"));
                continue;
            }

            if (!Directory.Exists(item.Path))
            {
                incomplete = true;
                events.Add(BlockedWorktree(item, "missing"));
                continue;
            }

            if (!HasGitMarker(item.Path))
            {
                incomplete = true;
                events.Add(BlockedWorktree(item, "unreadable"));
                continue;
            }

            if (item.GitDirectory is null)
            {
                incomplete = true;
                events.Add(BlockedWorktree(item, "unreadable"));
                continue;
            }

            if (remainingPaths.Any(path => IsNestedWorktree(item.Path, path)))
            {
                events.Add(BlockedWorktree(item, "nested_worktree"));
                continue;
            }

            var reason = LockAgeBlockReason(item, now) ?? ReclaimBlockReason(item, baseCommit, runner, now);
            if (reason is not null)
            {
                events.Add(BlockedWorktree(item, reason));
                continue;
            }

            if (force)
            {
                var removal = RemoveLane(repositoryRoot, item, baseCommit, runner, now,
                    protectObservedWorktree: Observe);
                events.Add(RemovalEvent(item, removal));
                CompleteRemoval(item, removal);
                continue;
            }

            var preview = WorktreeProtocolCommand.Run(repositoryRoot,
                ["remove", "--path", item.Path, "--preview"], runner, TimeSpan.FromSeconds(600));
            if (!preview.Success)
            {
                events.Add(BlockedWorktree(item, "identity_or_lock_refused"));
                incomplete = true;
                continue;
            }
            events.Add(new CleanLaneEvent(
                "stale_worktree",
                item.Path,
                item.Branch,
                item.Head,
                "would_remove",
                item.Locked ? "stale_lock" : "stale_behind"));
            remainingPaths.Remove(item.Path);
        }

        // Preview does not discharge a lock. Only that path's complete native removal
        // can do so; an unrelated success cannot clear incomplete attachment evidence.
        return !incomplete && retainedLocks.Count == 0;
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
            // 枚举与解析之间,别的会话可能合并后删掉了该分支;缺 ref 只跳过这一项。
            var head = TryResolveBranchCommit(repositoryRoot, branch, runner);
            if (head is null)
            {
                events.Add(new CleanLaneEvent(
                    "orphan_branch",
                    null,
                    branch,
                    null,
                    "skipped",
                    "vanished"));
                continue;
            }

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

            if (!DeleteObservedRef(repositoryRoot, branch, head, runner, preview: !force))
            {
                events.Add(new CleanLaneEvent("orphan_branch", null, branch, head,
                    "skipped", "remote_preservation_or_use_unconfirmed"));
                continue;
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
        string commonGitDirectory,
        bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        IReadOnlyList<string> tempRoots,
        ICollection<CleanLaneEvent> events,
        IWorktreeProcessRunner runner)
    {
        var registeredPaths = inventory.Select(static item => item.Path).ToHashSet(StringComparer.Ordinal);
        var registeredGitDirectories = inventory
            .Where(static item => item.GitDirectory is not null)
            .Select(static item => item.GitDirectory!)
            .ToHashSet(StringComparer.Ordinal);
        foreach (var path in tempRoots
            .Where(Directory.Exists)
            .Select(ResolveDirectoryPath)
            .SelectMany(static root => Directory.EnumerateDirectories(
                root,
                "trureturing-*",
                SearchOption.TopDirectoryOnly))
            .Select(Path.GetFullPath)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal))
        {
            if (registeredPaths.Contains(path)) continue;
            if (registeredPaths.Any(registered => IsNestedWorktree(path, registered)))
            {
                events.Add(new CleanLaneEvent("temp_judge", path, null, null,
                    "skipped", "nested_worktree"));
                continue;
            }
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
                && registeredGitDirectories.Contains(scannedGitDirectory))
            {
                // Freshly observed registrations also stay under the lane policy.
                continue;
            }

            var sameRepository = HasSameRepositoryPointer(path, commonGitDirectory);
            var gitlessJudge = !HasGitMarker(path) && HasGitlessJudgeShape(path);
            if (!sameRepository && !gitlessJudge)
            {
                events.Add(new CleanLaneEvent("temp_judge", path, null, null,
                    "skipped", HasGitMarker(path) ? "foreign_git_directory" : "not_judge_tree"));
                continue;
            }

            if (force)
            {
                try
                {
                    Directory.Delete(path, recursive: true);
                }
                catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
                {
                    events.Add(new CleanLaneEvent("temp_judge", path, null, null,
                        "partially_removed", "temporary_directory_partial_or_indeterminate"));
                    continue;
                }
            }

            events.Add(new CleanLaneEvent("temp_judge", path, null, null,
                force ? "removed" : "would_remove",
                sameRepository ? "unregistered_same_repository" : "gitless_judge_snapshot"));
        }
    }

    private static bool DeleteObservedRef(
        string repositoryRoot, string branch, string observedHead, IWorktreeProcessRunner runner,
        bool preview = false)
    {
        var arguments = new List<string> { "retire-branch", "--branch", branch, "--commit", observedHead };
        if (preview) arguments.Add("--preview");
        return WorktreeProtocolCommand.Run(repositoryRoot, arguments, runner).Success;
    }

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
        && Directory.Exists(Path.Combine(path, "tools"));

    private static string ResolveCommit(
        string repositoryRoot,
        string revision,
        IWorktreeProcessRunner runner) =>
        Decode(RunGit(
            repositoryRoot,
            ["rev-parse", "--verify", "--end-of-options", $"{revision}^{{commit}}"],
            runner,
            $"revision does not resolve: {revision}").StandardOutput).Trim();

    private static string? TryResolveBranchCommit(
        string repositoryRoot,
        string branch,
        IWorktreeProcessRunner runner)
    {
        var result = runner.Run(
            "git",
            ["rev-parse", "-q", "--verify", "--end-of-options", $"refs/heads/{branch}^{{commit}}"],
            repositoryRoot,
            TimeSpan.FromSeconds(120));
        if (result.ExitCode == 0) return Decode(result.StandardOutput).Trim();
        if (result.ExitCode == 1 && result.StandardOutput.Length == 0) return null;
        var error = Decode(result.StandardError).Trim();
        throw new InvalidOperationException(
            error.Length == 0 ? $"revision does not resolve: refs/heads/{branch}" : error);
    }

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

    private static bool IsNestedWorktree(string parent, string candidate) =>
        candidate.StartsWith(Path.TrimEndingDirectorySeparator(parent) + Path.DirectorySeparatorChar,
            StringComparison.Ordinal);

    private static string ResolveDirectoryPath(string path)
    {
        var directory = new DirectoryInfo(path);
        if (directory.Parent is null) return directory.FullName;
        var physical = new DirectoryInfo(Path.Combine(ResolveDirectoryPath(directory.Parent.FullName), directory.Name));
        return physical.ResolveLinkTarget(returnFinalTarget: true)?.FullName ?? physical.FullName;
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

    private sealed record CleanLaneEvent(
        string Kind,
        string? Path,
        string? Branch,
        string? Head,
        string Action,
        string Reason);
}
