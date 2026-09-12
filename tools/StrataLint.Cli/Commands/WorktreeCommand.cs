using System.Text;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record WorktreeOptions(
    string Branch,
    string Path,
    string Base,
    string Source,
    bool SkipRestore);

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
        "USAGE: StrataLint worktree ensure-cache [--path DIR] | "
        + "StrataLint worktree with-cache-reader [--path DIR] -- COMMAND [ARG ...] | StrataLint worktree warm-cache [--path DIR] | "
        + "StrataLint worktree validate-branch --branch NAME | "
        + "StrataLint worktree remove --names \"NAME [NAME ...]\" | "
        + "StrataLint worktree --kind KIND --name TASK_CODE --path DIR "
        + "[--base REV] [--source REPO_ROOT] [--skip-restore]. "
        + $"Allowed worktree kinds: {CreationKindList}. "
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
                runner);
        }
        if (arguments.Count > 0
            && string.Equals(arguments[0], "with-cache-reader", StringComparison.Ordinal))
        {
            return LeanCacheEnsureCommand.Run(
                repositoryRoot,
                arguments.Skip(1).ToArray(),
                runner,
                runCommand: true);
        }
        if (arguments.Count > 0 && arguments[0] == "warm-cache")
            return LeanCacheWarmCommand.Run(repositoryRoot, arguments.Skip(1).ToArray(), runner, cloner);
        if (arguments.Count > 0
            && string.Equals(arguments[0], "validate-branch", StringComparison.Ordinal))
        {
            return ValidateBranch(arguments.Skip(1).ToArray());
        }

        WorktreeOptions? options = null;
        var branchCreated = false;
        var worktreeCreated = false;
        string? branchOid = null;
        string? creationLock = null;
        string? creationMetadata = null;
        WorktreeBranchTracking? branchTracking = null;
        var halfBuiltRecovered = false;
        try
        {
            options = ParseArguments(repositoryRoot, arguments);
            halfBuiltRecovered = ValidatePreflight(options, runner);
            GitWorktreeInventory.FetchRemoteBase(options.Source, options.Base, runner);
            branchOid = VerifyBase(options, runner);
            var pins = LeanPinSet.ReadBase(options.Source, branchOid, runner);
            branchTracking = WorktreeBranchTracking.Prepare(options, runner);

            creationLock = $"worktree-init:{Guid.NewGuid():N}";
            RunRequired(
                runner,
                "git",
                ["update-ref", "--no-deref", "--create-reflog", "-m", creationLock,
                    $"refs/heads/{options.Branch}", branchOid, new string('0', branchOid.Length)],
                options.Source,
                BoundedProcessRunner.HangDetectionBudget,
                "git branch creation failed");
            branchCreated = true;
            branchTracking?.Apply(options, runner);
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
            WorktreeCreationSafety.CheckoutCreatedWorktree(options, runner);
            EnsureReviewScaffoldIgnores(options.Path);
            if (!options.SkipRestore)
            {
                RunRequired(
                    runner,
                    "dotnet",
                    ["restore", SolutionPath, "--locked-mode"],
                    options.Path,
                    TimeSpan.FromSeconds(1800),
                    "dotnet restore failed");
            }
            WorktreeCreationSafety.ValidateCreatedWorktree(options, runner);
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
                halfbuilt_recovered = halfBuiltRecovered,
                dotnet_restore = options.SkipRestore ? "skipped" : "restored",
            }) + "\n";
            return new CommandResult(true, summary, string.Empty);
        }
        catch (Exception exception)
        {
            var cleanup = string.Empty;
            try
            {
                // Either Git command can finish before acknowledging success.
                if (options is not null && creationLock is not null && branchOid is not null)
                {
                    creationMetadata ??= WorktreeCreationSafety.FindCreationMetadata(options, creationLock, runner);
                    if (worktreeCreated || creationMetadata is not null)
                        cleanup = Cleanup(options, creationLock, creationMetadata, runner);
                    if (cleanup.Length == 0)
                    {
                        WorktreeCreationSafety.CleanupCreatedBranch(options, creationLock, branchOid, branchCreated, runner);
                        branchTracking?.Rollback(options, runner);
                    }
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
                base_revision = options?.Base,
                reason = exception.Message,
                cleanup_error = cleanup.Length == 0 ? null : cleanup.TrimStart(';', ' '),
            });
            return new CommandResult(
                false,
                string.Empty,
                $"WORKTREE_FAILED {receipt}\n");
        }
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

        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
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
            skipRestore);
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
        var removal = RunProcess(
            runner,
            "git",
            ["worktree", "remove", "--force", "--force", options.Path],
            options.Source,
            BoundedProcessRunner.HangDetectionBudget);
        if (removal.ExitCode != 0)
        {
            try
            {
                WorktreeCreationSafety.ValidateCleanupOwnership(options, creationLock, creationMetadata, runner);
                if (Directory.Exists(options.Path)) Directory.Delete(options.Path, recursive: true);
                if (creationMetadata is not null && Directory.Exists(creationMetadata))
                    Directory.Delete(creationMetadata, recursive: true);
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                return $"; cleanup failed: {ProcessError(removal, "git worktree remove failed")}; {exception.Message}";
            }
        }

        return string.Empty;
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
