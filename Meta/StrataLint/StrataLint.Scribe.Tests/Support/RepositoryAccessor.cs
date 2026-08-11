using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

internal readonly record struct RepositoryRoot
{
    internal RepositoryRoot(string fullPath) => FullPath = fullPath;

    internal string FullPath { get; }
}

internal readonly record struct RepositoryRelativePath
{
    private RepositoryRelativePath(string value) => Value = value;

    internal string Value { get; }

    internal static RepositoryRelativePath Create(string value)
    {
        if (string.IsNullOrWhiteSpace(value)
            || Path.IsPathRooted(value)
            || value.Split('/', '\\').Any(static segment => segment is "" or "." or ".."))
        {
            throw new ArgumentException("repository path must be a normalized relative path", nameof(value));
        }

        return new RepositoryRelativePath(value.Replace('\\', '/'));
    }

    public override string ToString() => Value;
}

internal sealed class RepositoryAccessor
{
    private const string RootMarkerPath = "CLAUDE.md";
    private readonly HashSet<RepositoryRelativePath> accessedPaths = [];

    private RepositoryAccessor(RepositoryRoot root) => Root = root;

    internal RepositoryRoot Root { get; }

    internal IReadOnlySet<RepositoryRelativePath> AccessedPaths => accessedPaths;

    internal static RepositoryAccessor Discover()
    {
        for (var current = new DirectoryInfo(AppContext.BaseDirectory);
             current is not null;
             current = current.Parent)
        {
            if (File.Exists(Path.Combine(current.FullName, RootMarkerPath)))
            {
                return new RepositoryAccessor(new RepositoryRoot(current.FullName));
            }
        }

        throw new InvalidOperationException("repository root not found");
    }

    internal string ReadAllText(RepositoryRelativePath path) =>
        File.ReadAllText(RecordAndResolve(path));

    internal byte[] ReadAllBytes(RepositoryRelativePath path) =>
        File.ReadAllBytes(RecordAndResolve(path));

    internal bool FileExists(RepositoryRelativePath path) => File.Exists(RecordAndResolve(path));

    internal string GetFullPath(RepositoryRelativePath path) => RecordAndResolve(path);

    internal void CopyTo(
        RepositoryRelativePath source,
        string destination,
        bool overwrite = false) =>
        File.Copy(RecordAndResolve(source), destination, overwrite);

    internal IReadOnlyList<RepositoryRelativePath> EnumerateFiles(
        RepositoryRelativePath directory,
        string searchPattern)
    {
        accessedPaths.Add(directory);
        var prefix = directory.Value + "/";
        return GitIndexRepositoryFiles.Enumerate(Root.FullPath)
            .Where(file => file.RelativePath.StartsWith(prefix, StringComparison.Ordinal)
                && Path.GetFileName(file.RelativePath).MatchesSimplePattern(searchPattern))
            .Select(file => RepositoryRelativePath.Create(file.RelativePath))
            .ToArray();
    }

    private string RecordAndResolve(RepositoryRelativePath path)
    {
        accessedPaths.Add(path);
        return Path.Combine(Root.FullPath, path.Value.Replace('/', Path.DirectorySeparatorChar));
    }
}

internal static class SimplePatternExtensions
{
    internal static bool MatchesSimplePattern(this string fileName, string pattern)
    {
        if (pattern.StartsWith('*') && pattern.IndexOf('*', 1) < 0)
        {
            return fileName.EndsWith(pattern[1..], StringComparison.Ordinal);
        }

        return string.Equals(fileName, pattern, StringComparison.Ordinal);
    }
}
