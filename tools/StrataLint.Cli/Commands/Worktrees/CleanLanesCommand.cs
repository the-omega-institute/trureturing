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
    private const long MinimumMergedLaneAgeSeconds = 3L * 60 * 60;
    private const long MinimumBehindCommits = 300;

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        DateTimeOffset now)
    {
        var caller = Directory.GetCurrentDirectory();
        try
        {
            return Run(repositoryRoot, arguments, new ProductionWorktreeProcessRunner(),
                DefaultTempRoots(), now, Directory.SetCurrentDirectory);
        }
        finally
        {
            if (Directory.Exists(caller)) Directory.SetCurrentDirectory(caller);
        }
    }

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IReadOnlyList<string> tempRoots,
        DateTimeOffset now,
        Action<string>? anchorProcess = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(tempRoots);
        try
        {
            var root = Path.GetFullPath(repositoryRoot);
            var options = ParseArguments(arguments);
            var devCommit = TryResolveDevCommit(root, runner);
            var baseCommit = options.Base is "origin/dev" or "refs/remotes/origin/dev"
                ? devCommit : ResolveCommit(root, options.Base, runner);
            var commonGitDirectory = ResolveCommonGitDirectory(root, runner);
            var inventory = ReadWorktrees(root, runner);
            root = inventory[0].Path; // Keep Git commands usable when the invoking linked tree is selected.
            // Native process startup can read the parent's cwd even when a
            // child's working directory is explicit. Inputs are resolved above.
            anchorProcess?.Invoke(root);
            var events = new List<CleanLaneEvent>();
            var protectedInventory = inventory.ToList();
            void ProtectObservedWorktree(RegisteredWorktree observed)
            {
                protectedInventory.Add(observed);
            }

            var extraSweepsAllowed = InspectRegisteredLanes(
                root,
                commonGitDirectory,
                baseCommit,
                devCommit,
                options.Force,
                inventory,
                events,
                runner,
                now,
                ProtectObservedWorktree);
            if (!options.LanesOnly && extraSweepsAllowed)
            {
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
            var globalFailures = events.Count(static item =>
                item.Action is "failed" or "partially_removed" && !IsSingleItemResult(item));
            var warnings = new StringBuilder();
            foreach (var item in events.Where(NeedsWarning)
                .GroupBy(static item => item.Path, StringComparer.Ordinal).Select(static group => group.First()))
            {
                warnings.Append(JsonSerializer.Serialize(new
                {
                    @event = "clean_lanes_warning", path = item.Path, action = item.Action,
                    reason = item.Reason, diagnostic = item.Diagnostic ?? item.SelectionDetail ?? item.Reason,
                }));
                warnings.Append('\n');
            }
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
                    diagnostic = item.Diagnostic,
                    recovery_branch = item.RecoveryBranch,
                    recovery_branch_candidate = item.RecoveryBranchCandidate,
                    native_locks = item.NativeLocks,
                    selection_reason = item.SelectionReason,
                    selection_detail = item.SelectionDetail,
                }));
                output.Append('\n');
            }

            output.Append(JsonSerializer.Serialize(new
            {
                @event = "clean_lanes_summary",
                status = globalFailures == 0 ? "succeeded" : "failed",
                mode = options.Force ? "force" : "dry_run",
                scope = options.LanesOnly ? "lanes_only" : "full",
                extra_sweeps = options.LanesOnly ? "not_requested"
                    : extraSweepsAllowed ? "completed" : "deferred",
                extra_sweeps_reason = !options.LanesOnly && !extraSweepsAllowed
                    ? "global_failure" : null,
                base_revision = options.Base,
                base_commit = baseCommit,
                dev_revision = "refs/remotes/origin/dev",
                dev_commit = devCommit,
                dev_state = devCommit is null ? "dev_unknown" : "known",
                item_count = events.Count,
                removable_count = events.Count(static item =>
                    item.Action is "would_remove" or "removed"),
                removed_count = events.Count(static item => item.Action == "removed"),
                partial_count = partialCount,
                failed_count = failedCount,
            }));
            output.Append('\n');
            return new CommandResult(
                globalFailures == 0,
                output.ToString(),
                warnings.ToString() + (globalFailures == 0 ? string.Empty
                    : $"CLEAN_LANES_PARTIAL_FAILURE count={globalFailures}\n"));
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
        string? baseCommit,
        string? devCommit,
        bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        ICollection<CleanLaneEvent> events,
        IWorktreeProcessRunner runner,
        DateTimeOffset now,
        Action<RegisteredWorktree> protectObservedWorktree)
    {
        var remainingPaths = inventory.Select(static item => item.Path).ToHashSet(StringComparer.Ordinal);
        void Observe(RegisteredWorktree observed)
        {
            protectObservedWorktree(observed);
        }

        void CompleteRemoval(RegisteredWorktree item, LaneRemovalResult removal)
        {
            if (removal.Outcome == LaneRemovalOutcome.Removed)
            {
                remainingPaths.Remove(item.Path);
            }
        }

        // Initial observations belong to the invocation, including idle paths.
        // Pool observations may supplement them but cannot authorize mutation
        // after this invocation failed to establish a tree's identity.
        var failedPaths = new HashSet<string>(StringComparer.Ordinal);
        foreach (var item in inventory.Where(item => item.IdentityFailure is not null))
        {
            failedPaths.Add(item.Path);
            events.Add(QualificationEvent(item, new QualificationResult(item.IdentityFailure, QualificationOutcome.Failed)));
        }
        var poolForce = force && failedPaths.Count == 0;
        var poolPaths = InspectIdlePool(repositoryRoot, devCommit, poolForce, inventory, events, runner,
            CompleteRemoval, Observe);
        var qualifications = QualifyLockedLanes(repositoryRoot, inventory.Where(item => item.Locked
            && !poolPaths.Contains(item.Path) && !failedPaths.Contains(item.Path) && item.Path != inventory[0].Path
            && item.GitDirectory is not null && item.GitDirectory != commonGitDirectory
            && Directory.Exists(item.Path) && HasGitMarker(item.Path)).ToArray(), runner);
        if (qualifications.TryGetValue(string.Empty, out var batchFailure))
        {
            events.Add(new CleanLaneEvent("worktree_qualification", null, null, null, "failed", batchFailure.Reason!));
        }
        // Account for every obtained failure before any later eligibility guard.
        foreach (var item in inventory)
        {
            var failure = qualifications.GetValueOrDefault(item.Path);
            if (failure?.Failed != true) continue;
            failedPaths.Add(item.Path);
            events.Add(QualificationEvent(item, failure));
        }
        foreach (var item in inventory.OrderByDescending(static item => item.Path.Length))
        {
            if (poolPaths.Contains(item.Path) || failedPaths.Contains(item.Path)) continue;
            if (string.Equals(item.Path, inventory[0].Path, StringComparison.Ordinal)
                || string.Equals(item.GitDirectory, commonGitDirectory, StringComparison.Ordinal))
            {
                events.Add(BlockedWorktree(item, "main_worktree"));
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

            if (remainingPaths.Any(path => IsNestedWorktree(item.Path, path)))
            {
                events.Add(BlockedWorktree(item, "nested_worktree"));
                continue;
            }

            var qualification = qualifications.GetValueOrDefault(item.Path);
            if (qualification?.Reason is not null)
            {
                events.Add(QualificationEvent(item, qualification));
                continue;
            }

            var selection = SelectForReclaim(item, baseCommit, devCommit, runner, now);
            if (selection.BlockReason is not null)
            {
                events.Add(WithSelection(BlockedWorktree(item, selection.BlockReason), selection));
                continue;
            }

            if (force)
            {
                var removal = RemoveLane(repositoryRoot, item, baseCommit, devCommit, selection, runner, now,
                    protectObservedWorktree: Observe);
                events.Add(WithSelection(RemovalEvent(item, removal), selection));
                CompleteRemoval(item, removal);
                continue;
            }

            var preview = qualification ?? PreviewLane(repositoryRoot, item, runner);
            if (preview.Reason is not null)
            {
                events.Add(WithSelection(QualificationEvent(item, preview), selection));
                continue;
            }
            events.Add(WithSelection(new CleanLaneEvent(
                "stale_worktree",
                item.Path,
                item.Branch,
                item.Head,
                "would_remove",
                selection.RemovalReason(item.Locked)), selection));
            remainingPaths.Remove(item.Path);
        }

        // Per-tree refusals and failures retain their own paths. Only
        // failures without a tree identity defer the independent extra sweeps.
        return !events.Any(static item => item.Path is null
            && item.Action is "failed" or "partially_removed");
    }

    private static bool IsSingleWorktreeResult(CleanLaneEvent item) => item.Path is not null
        && item.Kind is "stale_worktree" or "lane_worktree" or "idle_worktree";

    private static bool IsSingleItemResult(CleanLaneEvent item) => IsSingleWorktreeResult(item)
        || item.Path is not null && item.Kind == "temp_judge";

    private static bool NeedsWarning(CleanLaneEvent item) => IsSingleItemResult(item)
        && (item.Action is "failed" or "partially_removed" or "deferred"
            || IsSingleWorktreeResult(item) && item.Action == "skipped"
                && (item.SelectedForRemoval || item.Reason is not
                    ("main_worktree" or "nested_worktree" or "recently_updated" or "not_far_behind"
                    or "locked_recent" or "initialization_in_progress" or "idle_pool" or "idle_locked" or "idle_dirty")));

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
                        "partially_removed", "temporary_directory_partial_or_indeterminate",
                        Diagnostic: exception.GetType().Name + ":" + BoundedDiagnostic(exception.Message)));
                    continue;
                }
            }

            events.Add(new CleanLaneEvent("temp_judge", path, null, null,
                force ? "removed" : "would_remove",
                sameRepository ? "unregistered_same_repository" : "gitless_judge_snapshot"));
        }
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

    private static CleanLaneEvent WithSelection(CleanLaneEvent item, ReclaimSelection selection) =>
        item with { SelectionReason = selection.Reason, SelectionDetail = selection.Detail,
            SelectedForRemoval = selection.BlockReason is null };

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
        string Reason,
        string? RecoveryBranch = null,
        string? RecoveryBranchCandidate = null,
        string? SelectionReason = null,
        string? SelectionDetail = null,
        JsonElement? NativeLocks = null,
        string? Diagnostic = null,
        bool SelectedForRemoval = false);
}
