using StrataLint.Runtime;
using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record WorktreeOptions(
    string Branch,
    string Path,
    string Base,
    string Source,
    bool SkipRestore,
    bool PreferIdle = false);

internal static class WorktreeCommand
{
    internal const string SolutionPath = "tools/StrataLint.sln";
    internal const string CreationNamespace = "lane";
    internal const string HistoricalLifecycleNamespace = "harness";
    internal const int BranchGrammarNonconformingExitCode = 1;
    internal const int UsageExitCode = 64;

    internal static IReadOnlyList<string> LifecycleNamespaces { get; } =
        [CreationNamespace, HistoricalLifecycleNamespace];

    internal static IReadOnlyList<string> CreationKinds { get; } =
        ["math", "governance", "theory"];

    private static string CreationKindList => string.Join(", ", CreationKinds);

    internal static string Usage { get; } =
        "USAGE: StrataLint worktree with [--path DIR] [--read PATH] [--write PATH] [--git] -- COMMAND [ARG ...] | "
        + "StrataLint worktree checkpoint --message-file FILE | "
        + "StrataLint worktree publish --branch NAME [--commit REV] | "
        + "StrataLint worktree finalize --branch NAME --writers-joined | "
        + "StrataLint worktree return [--pr N] --writers-joined | "
        + "StrataLint worktree ensure-cache [--path DIR] [--restore-dependencies] | "
        + "StrataLint worktree ensure-cache [--path DIR] [--restore-dependencies] | "
        + "StrataLint worktree with-cache-writer [--path DIR] -- COMMAND [ARG ...] | "
        + "StrataLint worktree with-cache-reader [--path DIR] -- COMMAND [ARG ...] | "
        + "StrataLint worktree validate-branch --branch NAME | "
        + "StrataLint worktree remove --names \"NAME [NAME ...]\" [--force] | "
        + "StrataLint worktree --kind KIND --name TASK_CODE --path DIR "
        + "[--base REV] [--source REPO_ROOT] [--skip-restore]. "
        + $"Allowed worktree kinds: {CreationKindList}. "
        + "Repeat the same kind/name/path to resume an owned failed initialization. "
        + "The .lake cache is materialized by the first Lean command; symlink sharing is forbidden.\n"
        + RemoveWorktreesCommand.Usage;

    private static readonly string[] ReviewScaffoldIgnorePatterns =
    [
        ".caller-review-prompt.md",
        ".echo-review.md",
        ".sshx-*",
    ];

    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments) =>
        Run(repositoryRoot, arguments, new ProductionWorktreeProcessRunner());

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner) =>
        Run(repositoryRoot, arguments, runner, new ApfsDirectoryCloner());

    internal static CommandResult Run(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        IDirectoryCloner cloner)
    {
        ArgumentNullException.ThrowIfNull(arguments);
        ArgumentNullException.ThrowIfNull(runner);
        ArgumentNullException.ThrowIfNull(cloner);
        if (arguments.Count > 0 && arguments[0] is "with" or "checkpoint" or "publish" or "finalize" or "return")
            return WorktreeProtocolCommand.Run(repositoryRoot, arguments, runner, Timeout.InfiniteTimeSpan);
        if (arguments.Count > 0
            && string.Equals(arguments[0], "remove", StringComparison.Ordinal))
        {
            return RemoveWorktreesCommand.Run(repositoryRoot, arguments.Skip(1).ToArray(), runner);
        }
        if (arguments.Count > 0
            && string.Equals(arguments[0], "ensure-cache", StringComparison.Ordinal))
        {
            return LeanCacheEnsureCommand.Run(
                repositoryRoot,
                arguments.Skip(1).ToArray(),
                runner,
                cloner);
        }
        if (arguments.Count > 0
            && arguments[0] is "with-cache-writer" or "with-cache-reader")
        {
            return LeanCacheEnsureCommand.RunWithWriter(
                repositoryRoot,
                arguments.Skip(1).ToArray(),
                runner,
                cloner);
        }
        if (arguments.Count > 0
            && string.Equals(arguments[0], "validate-branch", StringComparison.Ordinal))
        {
            return ValidateBranch(arguments.Skip(1).ToArray());
        }

        WorktreeOptions? options = null;
        var worktreeCreated = false;
        string? branchOid = null;
        string? creationLock = null;
        string? creationMetadata = null;
        WorktreeBranchTracking? branchTracking = null;
        var halfBuiltRecovered = false;
        var stage = "preflight";
        int? failureExitCode = null;
        IDisposable? initializationScope = null;
        string? idleClaimFallback = null;
        try
        {
            if (runner is ProductionWorktreeProcessRunner production)
                runner = production.WithEnvironment(WorktreeProtocolCommand.InitializationEnvironment(repositoryRoot));
            options = ParseArguments(repositoryRoot, arguments);
            var attachedPath = WorktreePoolCommand.FindAttachedTaskPath(options, runner);
            if (attachedPath is not null)
                options = options with { Path = attachedPath };
            else
            {
                var claimed = WorktreePoolCommand.TryClaim(options, runner, out idleClaimFallback);
                if (claimed is not null) return claimed;
            }
            if (Directory.Exists(options.Path) || RunProcess(runner, "git",
                ["show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}"], options.Source,
                BoundedProcessRunner.HangDetectionBudget).ExitCode == 0)
            {
                stage = "recovery";
                var reused = RecoverInitialization(options, runner);
                if (!reused.Success)
                {
                    failureExitCode = Directory.Exists(options.Path) ? reused.ExitCode : null;
                    throw new InvalidOperationException(reused.Error);
                }
                if (LeanPinSet.TryReadWorktree(options.Path, out var reason) is null)
                    throw new InvalidOperationException(reason);
                return reused;
            }
            initializationScope = WorktreeInitializationScope.Acquire(options.Source, options.Path, options.Branch);
            halfBuiltRecovered = ValidatePreflight(options, runner);
            GitWorktreeInventory.FetchRemoteBase(options.Source, options.Base, runner);
            branchOid = VerifyBase(options, runner);
            var pins = LeanPinSet.ReadBase(options.Source, branchOid, runner);
            var donor = ProbeDonor(options, pins, runner);
            branchTracking = WorktreeBranchTracking.Prepare(options, runner);

            creationLock = $"worktree-init:{Guid.NewGuid():N}";
            stage = "branch";
            RunRequired(
                runner,
                "git",
                ["update-ref", "--no-deref", "--create-reflog", "-m", creationLock,
                    $"refs/heads/{options.Branch}", branchOid, new string('0', branchOid.Length)],
                options.Source,
                BoundedProcessRunner.HangDetectionBudget,
                "git branch creation failed");
            branchTracking?.Apply(options, runner);
            stage = "registration";
            RunRequired(
                runner,
                "git",
                ["worktree", "add", "--no-checkout", "--lock",
                    "--reason", creationLock, options.Path, options.Branch],
                options.Source,
                BoundedProcessRunner.HangDetectionBudget,
                "git worktree add failed");
            worktreeCreated = true;
            creationMetadata = WorktreeCreationSafety.FindCreationMetadata(options, creationLock, runner);
            WorktreeCreationSafety.ValidateCreatedWorktree(options, runner);
            stage = "checkout";
            WorktreeCreationSafety.CheckoutCreatedWorktree(options, runner);
            EnsureReviewScaffoldIgnores(options.Path);
            if (!options.SkipRestore)
            {
                stage = "restore";
                var restore = RunProcess(runner, "dotnet", ["restore", SolutionPath, "--locked-mode"],
                    options.Path, TimeSpan.FromSeconds(1800));
                if (restore.ExitCode != 0)
                {
                    throw new InvalidOperationException(ProcessError(restore, "dotnet restore failed"));
                }
            }
            WorktreeCreationSafety.ValidateCreatedWorktree(options, runner);
            stage = "unlock";
            RunRequired(
                runner,
                "git",
                ["worktree", "unlock", options.Path],
                options.Source,
                BoundedProcessRunner.HangDetectionBudget,
                "git worktree unlock failed");

            var summary = JsonSerializer.Serialize(new
            {
                @event = "worktree_init",
                status = "succeeded",
                branch = options.Branch,
                path = options.Path,
                base_revision = options.Base,
                pin_sha256 = pins.Sha256,
                donor_behind_base = donor.BehindBase,
                donor_cache_pin = donor.CachePin,
                halfbuilt_recovered = halfBuiltRecovered,
                dotnet_restore = options.SkipRestore ? "skipped" : "restored",
                idle_claim_fallback = idleClaimFallback,
            }) + "\n";
            return new CommandResult(true, summary, RenderDonorWarning(options, donor));
        }
        catch (Exception exception)
        {
            var cleanup = string.Empty;
            string? recoveryResult = null;
            try
            {
                // Either Git command can finish before acknowledging success.
                if (options is not null && creationLock is not null && branchOid is not null)
                {
                    creationMetadata ??= WorktreeCreationSafety.FindCreationMetadata(options, creationLock, runner);
                    if (worktreeCreated || creationMetadata is not null)
                        cleanup = Cleanup(options, creationLock, creationMetadata, runner);
                    // The runner has settled its owned commands before returning.
                    // The common recovery path takes its own exclusive descriptor.
                    initializationScope?.Dispose();
                    initializationScope = null;
                    var recovered = RecoverInitialization(options, runner, creationLock);
                    if (recovered.Success) recoveryResult = recovered.Output.Trim();
                    cleanup = recovered.Success ? string.Empty : "initialization worktree retained: " + recovered.Error.Trim();
                }
            }
            catch (Exception cleanupException) when (cleanupException is not OutOfMemoryException)
            {
                cleanup = cleanupException.Message;
            }
            var receipt = JsonSerializer.Serialize(new
            {
                @event = "worktree_init",
                status = "failed",
                branch = options?.Branch,
                path = options?.Path,
                target = options?.Path,
                stage,
                base_revision = options?.Base,
                reason = exception.Message,
                cleanup_error = cleanup.Length == 0 ? null : cleanup.TrimStart(';', ' '),
                retained_material = new { branch = options?.Branch, path = options?.Path },
                recovery_result = recoveryResult,
                recovery_action = "rerun make worktree with the same KIND/NAME/DEST; or reclaim the registered target with make worktree-remove",
            });
            return new CommandResult(
                false,
                string.Empty,
                $"WORKTREE_FAILED {receipt}\n", failureExitCode);
        }
        finally
        {
            initializationScope?.Dispose();
        }
    }

    /// <summary>
    /// 货源树的状态读数——**只读取,不修改**。
    ///
    /// 这是已删除的 `LeanDonorRefresh` 的对偶:那个设计发现货源陈旧就自己去 pull 并
    /// rebuild 别人的树,失败还被吞成一个不进收据的字符串;这里只把读数摆出来,连同一条
    /// 可以直接粘贴执行的命令,由人决定要不要去暖它。同一个信息需求,一个越界一个不越界。
    ///
    /// 两个判据都取最便宜的形态。落后多少提交只用 `HEAD` 与 base 两个引用,不引入任何
    /// 远端名字。缓存则只看 stamp 是否为本次 base 的 pin 而建,**刻意不验 mathlib 完整性**:
    /// 那要遍历八千多个文件,会把三秒的建树拖慢,而 stamp 匹配本来也不证明完整。故字段叫
    /// `cache_pin` 而不是 `warm` —— 不冒领它没证明的东西。
    ///
    /// 全程尽力而为:探不到就报 null / absent,绝不让建树失败。
    /// </summary>
    private sealed record DonorStatus(int? BehindBase, string CachePin);

    private static DonorStatus ProbeDonor(
        WorktreeOptions options,
        LeanPinSet basePins,
        IWorktreeProcessRunner runner)
    {
        int? behind = null;
        try
        {
            var counted = RunProcess(
                runner,
                "git",
                ["rev-list", "--count", "--end-of-options", $"HEAD..{options.Base}"],
                options.Source,
                BoundedProcessRunner.HangDetectionBudget);
            if (counted.ExitCode == 0
                && int.TryParse(
                    Encoding.UTF8.GetString(counted.StandardOutput).Trim(),
                    System.Globalization.NumberStyles.Integer,
                    System.Globalization.CultureInfo.InvariantCulture,
                    out var parsed))
            {
                behind = parsed;
            }
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException
            or InvalidOperationException
            or TimeoutException)
        {
            behind = null;
        }

        var lake = System.IO.Path.Combine(options.Source, ".lake");
        var cachePin = !Directory.Exists(lake)
            ? "absent"
            : LeanCacheStamp.Matches(lake, basePins, out _) ? "match" : "mismatch";
        return new DonorStatus(behind, cachePin);
    }

    /// <summary>
    /// 没有可报的就一个字都不说——否则 warning 会退化成人人略过的背景噪音。
    /// 有可报的则给命令,不给结论:读者不需要同意我的判断,只需要能照着做。
    /// </summary>
    private static string RenderDonorWarning(WorktreeOptions options, DonorStatus donor)
    {
        var problems = new List<string>();
        if (donor.BehindBase is int behind and > 0)
        {
            problems.Add($"is {behind} commit{(behind == 1 ? string.Empty : "s")} behind {options.Base}");
        }

        if (donor.CachePin == "absent")
        {
            problems.Add("has no Lean build cache");
        }
        else if (donor.CachePin == "mismatch")
        {
            problems.Add("has a Lean build cache built for different pins");
        }

        if (problems.Count == 0) return string.Empty;

        return $"WARNING donor {options.Source} {string.Join(" and ", problems)}.\n"
            + $"        Only the cache is affected; this worktree still branches from {options.Base}.\n"
            + "        It will provision its own cache, which works and just costs more.\n"
            + $"        To warm the donor:  cd {options.Source} && git pull --ff-only && make lean\n";
    }

    private static void EnsureReviewScaffoldIgnores(string worktreeRoot)
    {
        var ignorePath = System.IO.Path.Combine(worktreeRoot, ".gitignore");
        var content = File.Exists(ignorePath) ? File.ReadAllText(ignorePath) : string.Empty;
        var normalizedLines = content
            .Replace("\r\n", "\n", StringComparison.Ordinal)
            .Replace('\r', '\n')
            .Split('\n');
        var existing = normalizedLines.ToHashSet(StringComparer.Ordinal);
        var missing = ReviewScaffoldIgnorePatterns
            .Where(pattern => !existing.Contains(pattern))
            .ToArray();
        if (missing.Length == 0) return;

        var newline = DetectNewline(content);
        var separator = content.Length > 0 && content[^1] is not ('\r' or '\n')
            ? newline
            : string.Empty;
        File.AppendAllText(
            ignorePath,
            separator + string.Join(newline, missing) + newline,
            new UTF8Encoding(encoderShouldEmitUTF8Identifier: false));
    }

    private static string DetectNewline(string content)
    {
        var carriageReturn = content.IndexOf('\r');
        var lineFeed = content.IndexOf('\n');
        if (carriageReturn >= 0 && (lineFeed < 0 || carriageReturn < lineFeed))
        {
            return carriageReturn + 1 < content.Length && content[carriageReturn + 1] == '\n'
                ? "\r\n"
                : "\r";
        }

        return "\n";
    }

    internal static WorktreeOptions ParseArguments(
        string repositoryRoot,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(arguments);
        string? kind = null;
        string? name = null;
        string? path = null;
        var baseRevision = "origin/dev";
        var source = repositoryRoot;
        var skipRestore = false;
        var preferIdle = false;

        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--prefer-idle" when !preferIdle:
                    preferIdle = true;
                    break;
                case "--skip-restore" when !skipRestore:
                    skipRestore = true;
                    break;
                case "--kind" when kind is null:
                    kind = ReadValue(arguments, ref index, allowEmpty: true);
                    break;
                case "--name" when name is null:
                    name = ReadValue(arguments, ref index, allowEmpty: true);
                    break;
                case "--path" when path is null:
                    path = ReadValue(arguments, ref index);
                    break;
                case "--base" when baseRevision == "origin/dev":
                    baseRevision = ReadValue(arguments, ref index);
                    break;
                case "--source" when source == repositoryRoot:
                    source = ReadValue(arguments, ref index);
                    break;
                default:
                    throw new InvalidOperationException(Usage);
            }
        }

        if (kind is null || name is null || path is null)
        {
            throw new InvalidOperationException(Usage);
        }

        var branch = $"{CreationNamespace}/{kind}/{name}";
        ValidateBranchGrammar(branch);
        return new WorktreeOptions(
            branch,
            System.IO.Path.GetFullPath(path),
            baseRevision,
            System.IO.Path.GetFullPath(source),
            skipRestore,
            preferIdle);
    }

    private static string ReadValue(
        IReadOnlyList<string> arguments,
        ref int index,
        bool allowEmpty = false)
    {
        if (++index >= arguments.Count || (!allowEmpty && arguments[index].Length == 0))
        {
            throw new InvalidOperationException(Usage);
        }

        return arguments[index];
    }

    internal static bool IsManagedBranch(string branch) =>
        LifecycleNamespaces.Any(candidate => HasNonEmptyNamespacePath(branch, candidate));

    internal static bool IsValidCreationBranch(string branch, out string reason)
    {
        var historicalNamespace = LifecycleNamespaces.FirstOrDefault(candidate =>
            !string.Equals(candidate, CreationNamespace, StringComparison.Ordinal)
            && HasNonEmptyNamespacePath(branch, candidate));
        if (historicalNamespace is not null)
        {
            reason = $"namespace '{historicalNamespace}' is a historical lifecycle namespace "
                + "managed only for cleanup and is not a creation alias; "
                + $"branch must match {CreationNamespace}/<kind>/<task-code>";
            return false;
        }

        var fields = branch.Split('/');
        var valid = fields.Length == 3
            && fields[0] == CreationNamespace
            && CreationKinds.Contains(fields[1], StringComparer.Ordinal)
            && fields[2].Length > 0;
        reason = valid
            ? string.Empty
            : CreationGrammarError(
                $"branch must match {CreationNamespace}/<kind>/<task-code>");
        return valid;
    }

    private static bool HasNonEmptyNamespacePath(string branch, string candidate) =>
        branch.StartsWith(candidate + "/", StringComparison.Ordinal)
        && branch.Length > candidate.Length + 1;

    private static string CreationGrammarError(string prefix) =>
        $"{prefix}; kind must be one of: {CreationKindList}";

    private static void ValidateBranchGrammar(string branch)
    {
        if (!IsValidCreationBranch(branch, out var reason))
        {
            throw new InvalidOperationException(reason);
        }
    }

    private static CommandResult ValidateBranch(IReadOnlyList<string> arguments)
    {
        if (arguments.Count != 2
            || !string.Equals(arguments[0], "--branch", StringComparison.Ordinal)
            || arguments[1].Length == 0)
        {
            return new CommandResult(
                false,
                string.Empty,
                "USAGE: StrataLint worktree validate-branch --branch NAME\n",
                UsageExitCode);
        }

        var branch = arguments[1];
        var canonical = IsValidCreationBranch(branch, out var reason);
        var output = JsonSerializer.Serialize(new
        {
            @event = "branch_validation",
            status = canonical ? "canonical" : "BRANCH_GRAMMAR_NONCONFORMING",
            branch,
            canonical,
            lifecycle_managed = IsManagedBranch(branch),
            reason = canonical ? null : reason,
        }) + "\n";
        return new CommandResult(
            canonical,
            output,
            string.Empty,
            canonical ? 0 : BranchGrammarNonconformingExitCode);
    }

    private static bool ValidatePreflight(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        if (!Directory.Exists(options.Source))
        {
            throw new InvalidOperationException($"source does not exist: {options.Source}");
        }

        var halfBuiltRecovered = WorktreeCreationSafety.RecoverHalfBuiltWorktree(options, runner);
        if (File.Exists(options.Path) || Directory.Exists(options.Path))
        {
            throw new InvalidOperationException($"path already exists: {options.Path}");
        }

        var branchFormat = RunProcess(
            runner,
            "git",
            ["check-ref-format", "--branch", options.Branch],
            options.Source,
            BoundedProcessRunner.HangDetectionBudget);
        if (branchFormat.ExitCode != 0)
        {
            throw new InvalidOperationException(
                CreationGrammarError(
                    $"branch must be a valid git ref matching "
                    + $"{CreationNamespace}/<kind>/<task-code>"));
        }

        var existingBranch = RunProcess(
            runner,
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}"],
            options.Source,
            BoundedProcessRunner.HangDetectionBudget);
        if (existingBranch.ExitCode == 0)
        {
            throw new InvalidOperationException($"branch already exists: {options.Branch}");
        }

        if (existingBranch.ExitCode != 1)
        {
            throw new InvalidOperationException(ProcessError(existingBranch, "could not inspect branch"));
        }

        return halfBuiltRecovered;
    }

    private static string VerifyBase(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        var result = RunProcess(
            runner,
            "git",
            ["rev-parse", "--verify", "--end-of-options", $"{options.Base}^{{commit}}"],
            options.Source,
            BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode != 0)
            throw new InvalidOperationException(ProcessError(result, $"base revision does not resolve: {options.Base}"));
        return Encoding.UTF8.GetString(result.StandardOutput).Trim();
    }

    private static string Cleanup(
        WorktreeOptions options,
        string creationLock,
        string? creationMetadata,
        IWorktreeProcessRunner runner)
    {
        WorktreeCreationSafety.ValidateCleanupOwnership(options, creationLock, creationMetadata, runner);
        return "initialization material retained for same-DEST recovery or reclaim";
    }

    internal static CommandResult RecoverInitialization(WorktreeOptions options,
        IWorktreeProcessRunner runner, string? token = null)
    {
        var arguments = new List<string> { "recover-init", "--path", options.Path,
            "--branch", options.Branch, "--base", options.Base };
        if (options.SkipRestore) arguments.Add("--skip-restore");
        if (token is not null) arguments.AddRange(["--expected-token", token]);
        return WorktreeProtocolCommand.Run(options.Source, arguments, runner, Timeout.InfiniteTimeSpan);
    }

    private static void RunRequired(
        IWorktreeProcessRunner runner,
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout,
        string fallback)
    {
        var result = RunProcess(runner, fileName, arguments, workingDirectory, timeout);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(ProcessError(result, fallback));
        }
    }

    private static ProcessOutput RunProcess(
        IWorktreeProcessRunner runner,
        string fileName,
        IReadOnlyList<string> arguments,
        string workingDirectory,
        TimeSpan timeout) =>
        runner.Run(fileName, arguments, workingDirectory, timeout);

    private static string ProcessError(ProcessOutput output, string fallback)
    {
        var error = Encoding.UTF8.GetString(output.StandardError).Trim();
        return error.Length == 0 ? fallback : error;
    }
}
