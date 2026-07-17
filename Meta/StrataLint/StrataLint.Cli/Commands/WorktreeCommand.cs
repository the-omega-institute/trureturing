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
    internal const string SolutionPath = "Meta/StrataLint/StrataLint.sln";
    internal const string Usage =
        "USAGE: StrataLint worktree --branch NAME --path DIR "
        + "[--base REV] [--source REPO_ROOT] [--skip-restore]. "
        + ".lake caches are copied for isolation; symlink sharing is forbidden.";

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
        IWorktreeProcessRunner runner)
    {
        ArgumentNullException.ThrowIfNull(runner);
        WorktreeOptions? options = null;
        var worktreeCreated = false;
        var stopwatch = System.Diagnostics.Stopwatch.StartNew();
        try
        {
            options = ParseArguments(repositoryRoot, arguments);
            ValidatePreflight(options, runner);
            GitWorktreeInventory.FetchRemoteBase(options.Source, options.Base, runner);
            VerifyBase(options, runner);
            var pins = LeanPinSet.ReadBase(options.Source, options.Base, runner);
            var donor = GitWorktreeInventory.SelectDonor(options.Source, pins, runner);

            RunRequired(
                runner,
                "git",
                ["worktree", "add", "-b", options.Branch, options.Path, options.Base],
                options.Source,
                TimeSpan.FromSeconds(120),
                "git worktree add failed");
            worktreeCreated = true;
            var cache = LeanCacheProvisioner.Provision(donor, options.Path, runner);
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
                branch = options.Branch,
                path = options.Path,
                base_revision = options.Base,
                donor = donor.Donor,
                pin_sha256 = pins.Sha256,
                cache_strategy = cache.Strategy,
                cache_method = cache.Method,
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
            var cleanup = options is not null && worktreeCreated
                ? Cleanup(options, runner)
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
