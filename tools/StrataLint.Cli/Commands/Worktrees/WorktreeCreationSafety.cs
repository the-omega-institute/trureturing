using System.Text;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class WorktreeCreationSafety
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

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

        var commonDirectoryResult = RunGit(
            options.Source,
            ["rev-parse", "--git-common-dir"],
            runner,
            "could not inspect git common directory");
        var commonDirectory = StrictUtf8.GetString(commonDirectoryResult.StandardOutput).Trim();
        if (commonDirectory.Length == 0)
        {
            throw new InvalidOperationException("could not inspect git common directory");
        }
        if (!Path.IsPathFullyQualified(commonDirectory))
        {
            commonDirectory = Path.Combine(options.Source, commonDirectory);
        }

        var expectedParent = PhysicalPathAllowMissing(Path.Combine(commonDirectory, "worktrees"));
        var actualParent = Path.GetDirectoryName(metadataPath);
        return actualParent is not null
            && PathsEqual(expectedParent, PhysicalPathAllowMissing(actualParent));
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
