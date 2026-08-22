using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record CleanLanesOptions(string Base, bool Force);

internal static class CleanLanesCommand
{
    internal const string Usage = "USAGE: StrataLint clean-lanes [--base REV] [--force]";

    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments) =>
        Run(
            repositoryRoot,
            arguments,
            new ProductionWorktreeProcessRunner(),
            DefaultTempRoots());

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IReadOnlyList<string> tempRoots)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(tempRoots);
        try
        {
            var options = ParseArguments(arguments);
            var events = new List<CleanLaneEvent>();
            var baseCommit = Inspect(
                repositoryRoot,
                options.Base,
                options.Force,
                new CleanLaneScope.Full(tempRoots),
                runner,
                events);

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
                base_revision = options.Base,
                base_commit = baseCommit,
                item_count = events.Count,
                removable_count = events.Count(static item =>
                    item.Action is "would_remove" or "removed"),
                removed_count = events.Count(static item => item.Action == "removed"),
            }));
            output.Append('\n');
            return new CommandResult(true, output.ToString(), string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"CLEAN_LANES_FAILED {exception.Message}\n");
        }
    }

    /// <summary>
    /// 回收的作用面。**这是一个类型,不是一个布尔**:`RegisteredLanes` 根本没有地方能放
    /// tempRoots,于是「建树时顺带回收」在结构上够不到 `/tmp` 里的判官树——那些树可能
    /// 正被席位用着,而它们的判据(未注册 / 无 .git 的快照)恰恰**区分不了「跑完了」和
    /// 「正在跑」**。孤儿分支同理:它不占一棵树,删它是纯分支操作,不属于「建树顺手回收
    /// 旧树」这件事。两者都留给显式的 `clean-lanes`——那是人按下的,不是顺带发生的。
    /// </summary>
    internal abstract record CleanLaneScope
    {
        private CleanLaneScope()
        {
        }

        /// <summary>只回收已注册的 lane worktree(连同它自己的分支)。</summary>
        internal sealed record RegisteredLanes : CleanLaneScope;

        /// <summary>注册 lane + 孤儿分支 + `tempRoots` 下的判官树。</summary>
        internal sealed record Full(IReadOnlyList<string> TempRoots) : CleanLaneScope;
    }

    /// <summary>
    /// 判词的唯一真源:`clean-lanes` 与建树时的顺带回收共用它,故两者的判据不可能漂移。
    /// 事件写进调用方给的集合而不是返回一个新列表——中途抛异常时,**已经发生的移除仍然
    /// 留在账上**,调用方据此如实报告,不至于把「删了三个然后炸了」报成「什么都没发生」。
    /// </summary>
    internal static string Inspect(
        string repositoryRoot,
        string baseRevision,
        bool force,
        CleanLaneScope scope,
        IWorktreeProcessRunner runner,
        ICollection<CleanLaneEvent> events)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(baseRevision);
        ArgumentNullException.ThrowIfNull(scope);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(events);
        var root = Path.GetFullPath(repositoryRoot);
        var baseCommit = ResolveCommit(root, baseRevision, runner);
        var currentGitDirectory = ResolveGitDirectory(root, runner);
        var inventory = ReadWorktrees(root, runner);
        InspectRegisteredLanes(
            root,
            currentGitDirectory,
            baseCommit,
            force,
            inventory,
            events,
            runner);
        if (scope is CleanLaneScope.Full full)
        {
            InspectOrphanBranches(
                root,
                baseCommit,
                force,
                inventory
                    .Where(static item => item.Branch is not null)
                    .Select(static item => item.Branch!)
                    .ToHashSet(StringComparer.Ordinal),
                events,
                runner);
            InspectTempJudges(
                root,
                ResolveCommonGitDirectory(root, runner),
                force,
                inventory,
                full.TempRoots,
                events,
                runner);
        }

        return baseCommit;
    }

    internal static CleanLanesOptions ParseArguments(IReadOnlyList<string> arguments)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        var baseRevision = "origin/dev";
        var baseSeen = false;
        var force = false;
        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--force" when !force:
                    force = true;
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

        return new CleanLanesOptions(baseRevision, force);
    }

    private static void InspectRegisteredLanes(
        string repositoryRoot,
        string currentGitDirectory,
        string baseCommit,
        bool force,
        IReadOnlyList<RegisteredWorktree> inventory,
        ICollection<CleanLaneEvent> events,
        IWorktreeProcessRunner runner)
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

            bool merged;
            try
            {
                merged = IsAncestor(repositoryRoot, item.Head, baseCommit, runner);
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                events.Add(BlockedWorktree(item, "unreadable"));
                continue;
            }

            if (!merged)
            {
                events.Add(BlockedWorktree(item, "unmerged"));
                continue;
            }

            if (force)
            {
                RemoveLane(repositoryRoot, item, runner);
            }

            events.Add(new CleanLaneEvent(
                "merged_worktree",
                item.Path,
                item.Branch,
                item.Head,
                force ? "removed" : "would_remove",
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
                "refs/heads/harness",
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

    private static void RemoveLane(
        string repositoryRoot,
        RegisteredWorktree item,
        IWorktreeProcessRunner runner)
    {
        var actualHead = Decode(RunGit(
            item.Path,
            ["rev-parse", "--verify", "HEAD^{commit}"],
            runner,
            "could not re-read lane head").StandardOutput).Trim();
        var actualBranch = Decode(RunGit(
            item.Path,
            ["branch", "--show-current"],
            runner,
            "could not re-read lane branch").StandardOutput).Trim();
        if (!string.Equals(actualHead, item.Head, StringComparison.Ordinal)
            || !string.Equals(actualBranch, item.Branch, StringComparison.Ordinal))
        {
            throw new InvalidOperationException($"lane identity changed during cleanup: {item.Path}");
        }

        var finalStatus = RunGit(
            item.Path,
            ["status", "--porcelain=v1", "-z", "--untracked-files=all"],
            runner,
            "could not re-read lane status");
        if (finalStatus.StandardOutput.Length != 0)
        {
            throw new InvalidOperationException($"lane became dirty during cleanup: {item.Path}");
        }

        RunGit(
            repositoryRoot,
            ["worktree", "remove", item.Path],
            runner,
            "could not remove merged lane worktree");
        DeleteObservedRef(repositoryRoot, item.Branch!, item.Head, runner);
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
                    TryResolveRegisteredGitDirectory(path, runner)));
                path = null;
                head = null;
                branch = null;
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
            TimeSpan.FromSeconds(30));
        return result.ExitCode == 0
            ? Decode(result.StandardOutput).Trim()
            : null;
    }

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
            TimeSpan.FromSeconds(30));
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
        string? GitDirectory);

    internal sealed record CleanLaneEvent(
        string Kind,
        string? Path,
        string? Branch,
        string? Head,
        string Action,
        string Reason);
}
