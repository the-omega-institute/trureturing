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
    internal const string Usage =
        "USAGE: StrataLint worktree ensure-cache [--path DIR] | "
        + "StrataLint worktree with-cache-writer [--path DIR] -- COMMAND [ARG ...] | "
        + "StrataLint worktree --branch NAME --path DIR "
        + "[--base REV] [--source REPO_ROOT] [--skip-restore]. "
        + ".lake caches are copied for isolation; symlink sharing is forbidden.";

    private static readonly string[] ReviewScaffoldIgnorePatterns =
    [
        ".caller-review-prompt.md",
        ".echo-review.md",
        ".sshx-*",
    ];

    private static readonly HashSet<string> OfficialRoles = new(StringComparer.Ordinal)
    {
        "adversary",
        "gate",
        "librarian",
        "numericist",
        "prover",
        "scout",
        "scribe",
        "theorist",
    };

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
            && string.Equals(arguments[0], "ensure-cache", StringComparison.Ordinal))
        {
            return LeanCacheEnsureCommand.Run(
                repositoryRoot,
                arguments.Skip(1).ToArray(),
                runner,
                cloner);
        }
        if (arguments.Count > 0
            && string.Equals(arguments[0], "with-cache-writer", StringComparison.Ordinal))
        {
            return LeanCacheEnsureCommand.RunWithWriter(
                repositoryRoot,
                arguments.Skip(1).ToArray(),
                runner,
                cloner);
        }

        WorktreeOptions? options = null;
        var worktreeCreated = false;
        var cleanupWorktreeOnFailure = false;
        var pruneOutcome = MathlibCachePruneOutcome.NotRun;
        var stopwatch = System.Diagnostics.Stopwatch.StartNew();
        try
        {
            options = ParseArguments(repositoryRoot, arguments);
            if (!LeanLakeExecutable.TryResolve(out var lakeExecutable, out var lakeReason))
            {
                throw new InvalidOperationException(lakeReason);
            }
            ValidatePreflight(options, runner);
            GitWorktreeInventory.FetchRemoteBase(options.Source, options.Base, runner);
            VerifyBase(options, runner);
            var pins = LeanPinSet.ReadBase(options.Source, options.Base, runner);
            using var donor = GitWorktreeInventory.SelectDonor(options.Source, pins, runner);

            RunRequired(
                runner,
                "git",
                ["worktree", "add", "-b", options.Branch, options.Path, options.Base],
                options.Source,
                TimeSpan.FromSeconds(120),
                "git worktree add failed");
            worktreeCreated = true;
            cleanupWorktreeOnFailure = true;
            EnsureReviewScaffoldIgnores(options.Path);
            using var targetWriter = LeanCacheWriterGuard.TryAcquire(
                Path.Combine(options.Path, ".lake"));
            if (targetWriter is null)
            {
                // A writer that won the post-add race owns the target cache now. Preserve the
                // worktree rather than deleting bytes underneath that live writer.
                cleanupWorktreeOnFailure = false;
                throw new InvalidOperationException("target cache writer guard is busy");
            }
            var cache = LeanCacheProvisioner.Provision(
                donor,
                options.Path,
                pins,
                lakeExecutable,
                runner,
                targetWriter,
                cloner);
            pruneOutcome = cache.PruneOutcome;
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

            stopwatch.Stop();
            var summary = JsonSerializer.Serialize(new
            {
                @event = "worktree_init",
                status = "succeeded",
                branch = options.Branch,
                path = options.Path,
                base_revision = options.Base,
                donor = donor.Donor,
                pin_sha256 = pins.Sha256,
                cache_strategy = cache.Strategy,
                cache_method = cache.Method,
                shared_cache_scope = pruneOutcome.Scope,
                mathlib_cache_pruned_files = pruneOutcome.DeletedFiles,
                mathlib_cache_clean_status = pruneOutcome.CleanStatus,
                dotnet_restore = options.SkipRestore ? "skipped" : "restored",
                elapsed_ms = stopwatch.ElapsedMilliseconds,
            }) + "\n";
            var warning = cache.Warning is null
                ? string.Empty
                : $"WORKTREE_WARNING {cache.Warning}\n";
            return new CommandResult(true, summary, warning);
        }
        catch (Exception exception)
        {
            stopwatch.Stop();
            if (exception is LeanCacheProvisionException cacheException)
            {
                pruneOutcome = cacheException.PruneOutcome;
            }
            var cleanup = options is not null && worktreeCreated && cleanupWorktreeOnFailure
                ? Cleanup(options, runner)
                : string.Empty;
            var receipt = JsonSerializer.Serialize(new
            {
                @event = "worktree_init",
                status = "failed",
                branch = options?.Branch,
                path = options?.Path,
                base_revision = options?.Base,
                reason = exception.Message,
                shared_cache_scope = pruneOutcome.Scope,
                mathlib_cache_pruned_files = pruneOutcome.DeletedFiles,
                mathlib_cache_clean_status = pruneOutcome.CleanStatus,
                cleanup_error = cleanup.Length == 0 ? null : cleanup.TrimStart(';', ' '),
                elapsed_ms = stopwatch.ElapsedMilliseconds,
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
        string? branch = null;
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
                case "--branch" when branch is null:
                    branch = ReadValue(arguments, ref index);
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

        if (branch is null || path is null)
        {
            throw new InvalidOperationException(Usage);
        }

        ValidateBranchGrammar(branch);
        return new WorktreeOptions(
            branch,
            System.IO.Path.GetFullPath(path),
            baseRevision,
            System.IO.Path.GetFullPath(source),
            skipRestore);
    }

    private static string ReadValue(IReadOnlyList<string> arguments, ref int index)
    {
        if (++index >= arguments.Count || arguments[index].Length == 0)
        {
            throw new InvalidOperationException(Usage);
        }

        return arguments[index];
    }

    internal static bool IsManagedBranch(string branch)
    {
        if (branch.StartsWith("harness/", StringComparison.Ordinal)
            && branch.Length > "harness/".Length)
        {
            return true;
        }

        var fields = branch.Split('/');
        return fields.Length == 3
            && fields[0] == "agent"
            && OfficialRoles.Contains(fields[1])
            && fields[2].Length > 0;
    }

    private static void ValidateBranchGrammar(string branch)
    {
        if (!IsManagedBranch(branch))
            throw new InvalidOperationException(
                "branch must match harness/* or agent/<official>/<task-code>");
    }

    private static void ValidatePreflight(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        if (!Directory.Exists(options.Source))
        {
            throw new InvalidOperationException($"source does not exist: {options.Source}");
        }

        if (File.Exists(options.Path) || Directory.Exists(options.Path))
        {
            throw new InvalidOperationException($"path already exists: {options.Path}");
        }

        var branchFormat = RunProcess(
            runner,
            "git",
            ["check-ref-format", "--branch", options.Branch],
            options.Source,
            TimeSpan.FromSeconds(30));
        if (branchFormat.ExitCode != 0)
        {
            throw new InvalidOperationException(
                "branch must be a valid git ref matching harness/* or agent/<official>/<task-code>");
        }

        var existingBranch = RunProcess(
            runner,
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}"],
            options.Source,
            TimeSpan.FromSeconds(30));
        if (existingBranch.ExitCode == 0)
        {
            throw new InvalidOperationException($"branch already exists: {options.Branch}");
        }

        if (existingBranch.ExitCode != 1)
        {
            throw new InvalidOperationException(ProcessError(existingBranch, "could not inspect branch"));
        }
    }

    private static void VerifyBase(WorktreeOptions options, IWorktreeProcessRunner runner) =>
        RunRequired(
            runner,
            "git",
            ["rev-parse", "--verify", "--end-of-options", $"{options.Base}^{{commit}}"],
            options.Source,
            TimeSpan.FromSeconds(30),
            $"base revision does not resolve: {options.Base}");

    private static string Cleanup(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        var errors = new List<string>();
        var removal = RunProcess(
            runner,
            "git",
            ["worktree", "remove", "--force", options.Path],
            options.Source,
            TimeSpan.FromSeconds(120));
        if (removal.ExitCode != 0 && Directory.Exists(options.Path))
        {
            errors.Add(ProcessError(removal, "git worktree remove failed"));
            try
            {
                Directory.Delete(options.Path, recursive: true);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
            {
                errors.Add(exception.Message);
            }
        }

        var branchLookup = RunProcess(
            runner,
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}"],
            options.Source,
            TimeSpan.FromSeconds(30));
        if (branchLookup.ExitCode == 0)
        {
            var branchRemoval = RunProcess(
                runner,
                "git",
                ["branch", "-D", options.Branch],
                options.Source,
                TimeSpan.FromSeconds(30));
            if (branchRemoval.ExitCode != 0)
            {
                errors.Add(ProcessError(branchRemoval, "git branch cleanup failed"));
            }
        }
        else if (branchLookup.ExitCode != 1)
        {
            errors.Add(ProcessError(branchLookup, "git branch cleanup inspection failed"));
        }

        return errors.Count == 0
            ? string.Empty
            : $"; cleanup failed: {string.Join("; ", errors)}";
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
