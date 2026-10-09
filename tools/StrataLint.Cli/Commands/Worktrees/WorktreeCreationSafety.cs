using StrataLint.Runtime;
using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class WorktreeCreationSafety
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static void CleanupCreatedBranch(
        WorktreeOptions options,
        string creationLock,
        string branchOid,
        bool branchCreated,
        IWorktreeProcessRunner runner)
    {
        var reference = $"refs/heads/{options.Branch}";
        var lookup = RunGit(options.Source,
            ["for-each-ref", "--format=%(refname)%09%(objectname)%09%(symref)", "--", reference],
            runner, "could not inspect initialization branch");
        var branch = StrictUtf8.GetString(lookup.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries)
            .Select(line => line.TrimEnd('\r').Split('\t'))
            .SingleOrDefault(fields => string.Equals(fields[0], reference, StringComparison.Ordinal));
        if (branch is null) return;

        if (branch.Length != 3 || branch[2].Length != 0
            || !string.Equals(branch[1], branchOid, StringComparison.Ordinal))
            throw new InvalidOperationException("initialization branch changed; refusing cleanup");

        // Creation acknowledgements become stale if the ref is deleted and recreated.
        var receipt = RunGit(options.Source,
            ["reflog", "show", "-1", "--format=%H%x09%gs", "--fixed-strings",
                $"--grep-reflog={creationLock}", reference, "--"],
            runner, "could not inspect initialization branch receipt");
        if (!string.Equals(StrictUtf8.GetString(receipt.StandardOutput).TrimEnd('\r', '\n'),
            $"{branchOid}\t{creationLock}", StringComparison.Ordinal))
        {
            if (branchCreated)
                throw new InvalidOperationException("initialization branch ownership changed; refusing cleanup");
            return;
        }

        ValidateBranchIsUnused(options, runner);
        _ = RunGit(options.Source, ["update-ref", "--no-deref", "-d", reference, branchOid],
            runner, "git branch cleanup failed");
    }

    private static void ValidateBranchIsUnused(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        var inventory = RunGit(options.Source, ["worktree", "list", "--porcelain", "-z"],
            runner, "could not inspect registered worktrees before branch cleanup");
        var expectedPath = PhysicalPathAllowMissing(options.Path);
        foreach (var record in StrictUtf8.GetString(inventory.StandardOutput)
            .Split("\0\0", StringSplitOptions.RemoveEmptyEntries))
        {
            var fields = record.Split('\0', StringSplitOptions.RemoveEmptyEntries);
            var path = fields.FirstOrDefault(field => field.StartsWith("worktree ", StringComparison.Ordinal));
            var branch = fields.FirstOrDefault(field => field.StartsWith("branch ", StringComparison.Ordinal));
            var head = fields.FirstOrDefault(field => field.StartsWith("HEAD ", StringComparison.Ordinal));
            // A partial registration can have neither a branch nor a usable HEAD yet.
            var partial = !fields.Contains("bare", StringComparer.Ordinal) && branch is null
                && (head is null || head["HEAD ".Length..].All(character => character == '0'));
            if (partial || string.Equals(branch, $"branch refs/heads/{options.Branch}", StringComparison.Ordinal)
                || (path is not null && PathsEqual(expectedPath, PhysicalPathAllowMissing(path["worktree ".Length..]))))
                throw new InvalidOperationException("initialization branch may be in use by a registered worktree; refusing cleanup");
        }
    }

    internal static string? FindCreationMetadata(
        WorktreeOptions options,
        string creationLock,
        IWorktreeProcessRunner runner)
    {
        var commonDirectory = ReadCommonDirectory(options, runner);
        var registry = Path.Combine(commonDirectory, "worktrees");
        if (!Directory.Exists(registry)) return null;
        if (File.GetAttributes(registry).HasFlag(FileAttributes.ReparsePoint))
            throw new InvalidOperationException("could not inspect initialization ownership through a linked registry");

        var expected = PhysicalPathAllowMissing(Path.Combine(options.Path, ".git"));
        string? owned = null;
        foreach (var metadata in Directory.EnumerateDirectories(registry))
        {
            try
            {
                if (File.GetAttributes(metadata).HasFlag(FileAttributes.ReparsePoint)
                    || !string.Equals(ReadMetadataValue(metadata, "locked"), creationLock, StringComparison.Ordinal))
                    continue;
            }
            catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
            {
                // Another cleanup can remove an unrelated registration during enumeration.
                continue;
            }

            // Git writes the lock and linking files before HEAD. The backlink also survives a corrupt .git pointer.
            var gitdir = ReadMetadataValue(metadata, "gitdir");
            var commondir = ReadMetadataValue(metadata, "commondir");
            if (gitdir is null || commondir is null
                || !PathsEqual(expected, PhysicalPathAllowMissing(Path.GetFullPath(gitdir, metadata)))
                || !PathsEqual(commonDirectory, PhysicalPathAllowMissing(Path.GetFullPath(commondir, metadata)))
                || owned is not null)
                throw new InvalidOperationException("could not validate initialization metadata ownership");
            owned = metadata;
        }
        return owned;
    }

    internal static void ValidateCleanupOwnership(
        WorktreeOptions options,
        string creationLock,
        string? metadata,
        IWorktreeProcessRunner runner)
    {
        var current = FindCreationMetadata(options, creationLock, runner);
        if (metadata is not null && PathEntryExists(metadata))
        {
            if (current is not null && PathsEqual(metadata, current)) return;
        }
        else if (current is null && !IsRegisteredWorktree(options, runner))
        {
            return;
        }
        throw new InvalidOperationException("initialization ownership changed; refusing cleanup");
    }

    private static string? ReadMetadataValue(string metadata, string name)
    {
        var path = Path.Combine(metadata, name);
        try
        {
            if (!File.Exists(path) || File.GetAttributes(path).HasFlag(FileAttributes.ReparsePoint)) return null;
            var value = File.ReadAllText(path, StrictUtf8).TrimEnd('\r', '\n');
            return value.Length > 0 && value.AsSpan().IndexOfAny('\r', '\n') < 0 ? value : null;
        }
        catch (Exception exception) when (exception is FileNotFoundException or DirectoryNotFoundException)
        {
            return null;
        }
    }

    internal static void CheckoutCreatedWorktree(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        _ = RunGit(options.Path, ["reset", "--hard", "--no-recurse-submodules", "HEAD"],
            runner, "git worktree checkout failed");
        var head = StrictUtf8.GetString(RunGit(options.Path, ["rev-parse", "--verify", "HEAD"],
            runner, "could not inspect created HEAD").StandardOutput).Trim();
        // Match worktree add's initialization event, including the repository's object ID width.
        _ = RunGit(options.Path,
            ["hook", "run", "--ignore-missing", "post-checkout", "--", new string('0', head.Length), head, "1"],
            runner, "git worktree post-checkout hook failed");
    }

    internal static bool RecoverHalfBuiltWorktree(
        WorktreeOptions options,
        IWorktreeProcessRunner runner)
    {
        if (!Directory.Exists(options.Path)
            || !HasMissingOwnedMetadata(options, runner)
            || IsRegisteredWorktree(options, runner))
        {
            return false;
        }

        var branchLookup = runner.Run(
            "git",
            ["show-ref", "--verify", "--quiet", $"refs/heads/{options.Branch}"],
            options.Source,
            BoundedProcessRunner.HangDetectionBudget);
        if (branchLookup.ExitCode == 0)
        {
            _ = RunGit(
                options.Source,
                ["branch", "-D", options.Branch],
                runner,
                "half-built worktree branch cleanup failed");
        }
        else if (branchLookup.ExitCode != 1)
        {
            throw new InvalidOperationException(
                ProcessError(branchLookup, "could not inspect half-built worktree branch"));
        }

        try
        {
            Directory.Delete(options.Path, recursive: true);
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            throw new InvalidOperationException(
                $"half-built worktree cleanup failed: {exception.Message}",
                exception);
        }

        return true;
    }

    internal static void ValidateCreatedWorktree(
        WorktreeOptions options,
        IWorktreeProcessRunner runner)
    {
        if (!IsRegisteredWorktree(options, runner))
        {
            throw new InvalidOperationException(
                $"created worktree is not registered: {options.Path}");
        }

        var topLevel = RunGit(
            options.Path,
            ["rev-parse", "--show-toplevel"],
            runner,
            $"created worktree is unusable: {options.Path}");
        var actualRoot = StrictUtf8.GetString(topLevel.StandardOutput).Trim();
        if (actualRoot.Length == 0
            || !PathsEqual(
                PhysicalPathAllowMissing(options.Path),
                PhysicalPathAllowMissing(actualRoot)))
        {
            throw new InvalidOperationException(
                $"created worktree resolved to an unexpected root: {actualRoot}");
        }
    }

    private static bool HasMissingOwnedMetadata(
        WorktreeOptions options,
        IWorktreeProcessRunner runner)
    {
        var gitFile = Path.Combine(options.Path, ".git");
        if (!File.Exists(gitFile)
            || File.GetAttributes(gitFile).HasFlag(FileAttributes.ReparsePoint))
        {
            return false;
        }

        var content = File.ReadAllText(gitFile).TrimEnd('\r', '\n');
        const string prefix = "gitdir: ";
        if (!content.StartsWith(prefix, StringComparison.Ordinal)
            || content.Length == prefix.Length
            || content.AsSpan(prefix.Length).IndexOfAny('\r', '\n') >= 0)
        {
            return false;
        }

        var rawMetadataPath = content[prefix.Length..];
        var metadataPath = Path.GetFullPath(
            Path.IsPathFullyQualified(rawMetadataPath)
                ? rawMetadataPath
                : Path.Combine(options.Path, rawMetadataPath));
        if (PathEntryExists(metadataPath)) return false;

        var expectedParent = PhysicalPathAllowMissing(Path.Combine(ReadCommonDirectory(options, runner), "worktrees"));
        var actualParent = Path.GetDirectoryName(metadataPath);
        return actualParent is not null
            && PathsEqual(expectedParent, PhysicalPathAllowMissing(actualParent));
    }

    private static string ReadCommonDirectory(WorktreeOptions options, IWorktreeProcessRunner runner)
    {
        var commonDirectoryResult = RunGit(
            options.Source,
            ["rev-parse", "--git-common-dir"],
            runner,
            "could not inspect git common directory");
        var commonDirectory = StrictUtf8.GetString(commonDirectoryResult.StandardOutput).TrimEnd('\r', '\n');
        if (commonDirectory.Length == 0)
        {
            throw new InvalidOperationException("could not inspect git common directory");
        }
        return PhysicalPathAllowMissing(Path.GetFullPath(commonDirectory, options.Source));
    }

    private static bool IsRegisteredWorktree(
        WorktreeOptions options,
        IWorktreeProcessRunner runner)
    {
        var inventory = RunGit(
            options.Source,
            ["worktree", "list", "--porcelain", "-z"],
            runner,
            "could not inspect registered worktrees");
        var expected = PhysicalPathAllowMissing(options.Path);
        return StrictUtf8.GetString(inventory.StandardOutput)
            .Split('\0', StringSplitOptions.RemoveEmptyEntries)
            .Where(static field => field.StartsWith("worktree ", StringComparison.Ordinal))
            .Select(static field => field["worktree ".Length..])
            .Any(path => PathsEqual(expected, PhysicalPathAllowMissing(path)));
    }

    private static ProcessOutput RunGit(
        string workingDirectory,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        string fallback)
    {
        var result = runner.Run(
            "git",
            arguments,
            workingDirectory,
            BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode == 0) return result;
        throw new InvalidOperationException(ProcessError(result, fallback));
    }

    private static string ProcessError(ProcessOutput output, string fallback)
    {
        var error = StrictUtf8.GetString(output.StandardError).Trim();
        return error.Length == 0 ? fallback : error;
    }

    private static string PhysicalPathAllowMissing(string path)
    {
        var current = Path.GetFullPath(path);
        var missingSegments = new Stack<string>();
        while (!PathEntryExists(current))
        {
            var parent = Path.GetDirectoryName(current);
            if (parent is null || PathsEqual(parent, current)) break;
            missingSegments.Push(Path.GetFileName(current));
            current = parent;
        }

        var resolved = LeanCacheGuard.PhysicalPath(current);
        while (missingSegments.TryPop(out var segment))
        {
            resolved = Path.Combine(resolved, segment);
        }
        return resolved;
    }

    private static bool PathEntryExists(string path)
    {
        try
        {
            _ = File.GetAttributes(path);
            return true;
        }
        catch (FileNotFoundException)
        {
            return false;
        }
        catch (DirectoryNotFoundException)
        {
            return false;
        }
    }

    private static bool PathsEqual(string left, string right) =>
        string.Equals(
            Path.TrimEndingDirectorySeparator(left),
            Path.TrimEndingDirectorySeparator(right),
            OperatingSystem.IsWindows()
                ? StringComparison.OrdinalIgnoreCase
                : StringComparison.Ordinal);
}
