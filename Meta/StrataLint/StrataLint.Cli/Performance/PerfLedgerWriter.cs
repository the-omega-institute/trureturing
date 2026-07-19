using System.Text;

namespace StrataLint.Cli;

internal static class PerfLedgerWriter
{
    internal static int Append(string repositoryRoot, string inputPath, string ledgerPath)
    {
        var repository = ResolvePath(repositoryRoot);
        var ledger = ResolvePath(ledgerPath);
        if (IsWithin(repository, ledger))
        {
            throw new InvalidOperationException("performance ledger must remain outside the repository");
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
        using var output = new FileStream(ledger, FileMode.Append, FileAccess.Write, FileShare.Read);
        output.Write(bytes);
        output.Flush(flushToDisk: true);
        return events.Length;
    }

    private static bool IsWithin(string root, string path)
    {
        var relative = Path.GetRelativePath(root, path);
        return !Path.IsPathRooted(relative)
            && !string.Equals(relative, "..", StringComparison.Ordinal)
            && !relative.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal);
    }

    private static string ResolvePath(string path)
    {
        var full = Path.GetFullPath(path);
        if (File.Exists(full))
        {
            return new FileInfo(full).ResolveLinkTarget(returnFinalTarget: true)?.FullName ?? full;
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
