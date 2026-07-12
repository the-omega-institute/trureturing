using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record WorktreeOptions(
    string Branch,
    string Path,
    string Base,
    string Source,
    bool Warm);

internal static class WorktreeCommand
{
    internal const string Usage =
        "USAGE: StrataLint worktree --branch NAME --path DIR "
        + "[--base REV] [--source REPO_ROOT] [--warm]";

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

    internal static CommandResult Run(string repositoryRoot, IReadOnlyList<string> arguments)
    {
        WorktreeOptions? options = null;
        var provisioningStarted = false;
        var stopwatch = System.Diagnostics.Stopwatch.StartNew();
        try
        {
            options = ParseArguments(repositoryRoot, arguments);
            Validate(options);
            provisioningStarted = true;
            RunRequired(
                "git",
                new[] { "worktree", "add", "-b", options.Branch, options.Path, options.Base },
                options.Source,
                TimeSpan.FromSeconds(120));
            var clone = LeanCacheCloner.Clone(options.Source, options.Path);
            if (options.Warm)
            {
                RunRequired(
                    "lake",
                    new[] { "build" },
                    options.Path,
                    TimeSpan.FromSeconds(1800));
            }

            stopwatch.Stop();
            var summary = $"WORKTREE path={options.Path} branch={options.Branch} "
                + $"clone={clone.Strategy} warm={options.Warm.ToString().ToLowerInvariant()} "
                + $"elapsed_ms={stopwatch.ElapsedMilliseconds}\n";
            var warning = clone.Warning is null
                ? string.Empty
                : $"WORKTREE_WARNING {clone.Warning}\n";
            return new CommandResult(true, summary, warning);
        }
        catch (Exception exception)
        {
            var cleanup = options is not null && provisioningStarted
                ? Cleanup(options)
                : string.Empty;
            return new CommandResult(
                false,
                string.Empty,
                $"WORKTREE_FAILED {exception.Message}{cleanup}\n");
        }
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
        var warm = false;

        for (var index = 0; index < arguments.Count; index++)
        {
            switch (arguments[index])
            {
                case "--warm" when !warm:
                    warm = true;
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
            warm);
    }

    private static string ReadValue(IReadOnlyList<string> arguments, ref int index)
    {
        if (++index >= arguments.Count || arguments[index].Length == 0)
        {
            throw new InvalidOperationException(Usage);
        }

        return arguments[index];
    }

    private static void ValidateBranchGrammar(string branch)
    {
        if (branch.StartsWith("harness/", StringComparison.Ordinal)
            && branch.Length > "harness/".Length)
        {
            return;
        }

        var fields = branch.Split('/');
        if (fields.Length == 3
            && fields[0] == "agent"
            && OfficialRoles.Contains(fields[1])
            && fields[2].Length > 0)
        {
            return;
        }

        throw new InvalidOperationException(
            "branch must match harness/* or agent/<official>/<task-code>");
    }

    private static void Validate(WorktreeOptions options)
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
            "git",
            new[] { "check-ref-format", "--branch", options.Branch },
            options.Source,
            TimeSpan.FromSeconds(30));
        if (branchFormat.ExitCode != 0)
        {
            throw new InvalidOperationException(
                "branch must be a valid git ref matching harness/* or agent/<official>/<task-code>");
        }

        var existingBranch = RunProcess(
            "git",
            new[] { "show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}" },
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

        RunRequired(
            "git",
            new[] { "rev-parse", "--verify", "--end-of-options", $"{options.Base}^{{commit}}" },
            options.Source,
            TimeSpan.FromSeconds(30));
    }

    private static string Cleanup(WorktreeOptions options)
    {
        var errors = new List<string>();
        var removal = RunProcess(
            "git",
            new[] { "worktree", "remove", "--force", options.Path },
            options.Source,
            TimeSpan.FromSeconds(120));
        if (removal.ExitCode != 0 && Directory.Exists(options.Path))
        {
            errors.Add(ProcessError(removal, "git worktree remove failed"));
            try
            {
                if (Directory.Exists(options.Path)) Directory.Delete(options.Path, recursive: true);
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
            {
                errors.Add(exception.Message);
            }
        }

        var branchLookup = RunProcess(
            "git",
            new[] { "show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}" },
            options.Source,
            TimeSpan.FromSeconds(30));
        if (branchLookup.ExitCode == 0)
        {
            var branchRemoval = RunProcess(
                "git",
                new[] { "branch", "-D", options.Branch },
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
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout)
    {
        var result = RunProcess(fileName, arguments, workingDirectory, timeout);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(ProcessError(result, $"{fileName} command failed"));
        }
    }

    private static ProcessOutput RunProcess(
        string fileName,
        IEnumerable<string> arguments,
        string workingDirectory,
        TimeSpan timeout) =>
        BoundedProcessRunner.Run(fileName, arguments, workingDirectory, timeout, 64 * 1024 * 1024);

    private static string ProcessError(ProcessOutput output, string fallback)
    {
        var error = System.Text.Encoding.UTF8.GetString(output.StandardError).Trim();
        return error.Length == 0 ? fallback : error;
    }
}
