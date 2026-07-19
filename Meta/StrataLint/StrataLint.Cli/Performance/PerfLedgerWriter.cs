using System.Text;

namespace StrataLint.Cli;

internal static class PerfLedgerWriter
{
    internal static int Append(string repositoryRoot, string inputPath, string ledgerPath)
    {
        var repository = ResolvePath(repositoryRoot);
        var ledger = ResolvePath(ledgerPath);
        if (RegisteredWorktreeRoots(repository).Any(root => IsWithin(root, ledger)))
        {
            throw new InvalidOperationException(
                "performance ledger must remain outside every registered worktree");
        }

        var events = File.ReadLines(inputPath)
            .Where(static line => !string.IsNullOrWhiteSpace(line))
            .Select(PerfEventCodec.ParseLine)
            .ToArray();
        if (events.Length == 0) return 0;

        var bytes = Encoding.UTF8.GetBytes(
            string.Concat(events.Select(static item => PerfEventCodec.WriteLine(item) + "\n")));
        Directory.CreateDirectory(Path.GetDirectoryName(ledger)
            ?? throw new InvalidOperationException("performance ledger requires a parent directory"));
        using var output = new FileStream(
            ledger,
            FileMode.OpenOrCreate,
            FileAccess.Write,
            FileShare.Read,
            bufferSize: 1);
        var initialLength = output.Length;
        output.Position = initialLength;
        try
        {
            output.Write(bytes);
            output.Flush(flushToDisk: true);
        }
        catch (Exception writeFailure) when (
            writeFailure is ArgumentException or IOException or UnauthorizedAccessException)
        {
            try
            {
                output.SetLength(initialLength);
                output.Flush(flushToDisk: true);
            }
            catch (Exception rollbackFailure) when (
                rollbackFailure is ArgumentException or IOException or UnauthorizedAccessException)
            {
                throw new IOException(
                    "performance ledger append and rollback both failed",
                    new AggregateException(writeFailure, rollbackFailure));
            }

            throw;
        }
        return events.Length;
    }

    private static bool IsWithin(string root, string path)
    {
        var comparison = OperatingSystem.IsLinux()
            ? StringComparison.Ordinal
            : StringComparison.OrdinalIgnoreCase;
        var normalizedRoot = Path.TrimEndingDirectorySeparator(ResolvePath(root));
        var normalizedPath = ResolvePath(path);
        return string.Equals(normalizedRoot, normalizedPath, comparison)
            || normalizedPath.StartsWith(
                normalizedRoot + Path.DirectorySeparatorChar,
                comparison);
    }

    private static IEnumerable<string> RegisteredWorktreeRoots(string repository)
    {
        yield return repository;

        var gitEntry = Path.Combine(repository, ".git");
        if (!Directory.Exists(gitEntry) && !File.Exists(gitEntry)) yield break;
        var gitDirectory = Directory.Exists(gitEntry)
            ? gitEntry
            : ReadGitDirectory(gitEntry, repository);
        var commonDirectory = ResolveCommonGitDirectory(gitDirectory);
        var mainRoot = Directory.GetParent(commonDirectory)?.FullName;
        if (mainRoot is not null) yield return mainRoot;

        var worktreesDirectory = Path.Combine(commonDirectory, "worktrees");
        if (!Directory.Exists(worktreesDirectory)) yield break;
        foreach (var metadataDirectory in Directory.EnumerateDirectories(worktreesDirectory))
        {
            var linkedGitEntry = ReadPathFile(
                Path.Combine(metadataDirectory, "gitdir"),
                metadataDirectory);
            var linkedRoot = Directory.GetParent(linkedGitEntry)?.FullName
                ?? throw new InvalidOperationException("registered worktree gitdir has no parent");
            yield return linkedRoot;
        }
    }

    private static string ResolveCommonGitDirectory(string gitDirectory)
    {
        var commonPath = Path.Combine(gitDirectory, "commondir");
        if (File.Exists(commonPath)) return ReadPathFile(commonPath, gitDirectory);

        var parent = Directory.GetParent(gitDirectory);
        if (parent is not null
            && string.Equals(parent.Name, "worktrees", StringComparison.Ordinal))
        {
            return parent.Parent?.FullName
                ?? throw new InvalidOperationException("linked worktree has no common git directory");
        }

        return gitDirectory;
    }

    private static string ReadGitDirectory(string gitFile, string repository)
    {
        var value = File.ReadAllText(gitFile).Trim();
        const string Prefix = "gitdir:";
        if (!value.StartsWith(Prefix, StringComparison.OrdinalIgnoreCase))
        {
            throw new InvalidOperationException("worktree .git file has an invalid format");
        }

        return ResolveReferencedPath(value[Prefix.Length..].Trim(), repository);
    }

    private static string ReadPathFile(string pathFile, string relativeTo)
    {
        var value = File.ReadAllText(pathFile).Trim();
        if (string.IsNullOrWhiteSpace(value))
        {
            throw new InvalidOperationException($"path file is empty: {pathFile}");
        }

        return ResolveReferencedPath(value, relativeTo);
    }

    private static string ResolveReferencedPath(string path, string relativeTo) =>
        ResolvePath(Path.IsPathRooted(path) ? path : Path.Combine(relativeTo, path));

    private static string ResolvePath(string path)
    {
        var full = Path.GetFullPath(path);
        if (File.Exists(full))
        {
            return new FileInfo(full).ResolveLinkTarget(returnFinalTarget: true)?.FullName ?? full;
        }
        if (Directory.Exists(full))
        {
            return new DirectoryInfo(full).ResolveLinkTarget(returnFinalTarget: true)?.FullName ?? full;
        }

        var tail = new Stack<string>();
        var current = new DirectoryInfo(Path.GetDirectoryName(full)
            ?? throw new InvalidOperationException("path requires a parent directory"));
        while (!current.Exists)
        {
            tail.Push(current.Name);
            current = current.Parent
                ?? throw new InvalidOperationException("path has no existing ancestor");
        }

        var resolved = current.ResolveLinkTarget(returnFinalTarget: true)?.FullName ?? current.FullName;
        while (tail.Count > 0) resolved = Path.Combine(resolved, tail.Pop());
        return Path.Combine(resolved, Path.GetFileName(full));
    }
}
