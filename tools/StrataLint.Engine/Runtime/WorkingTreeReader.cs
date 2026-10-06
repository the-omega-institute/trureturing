using System.Collections.Immutable;
using System.Runtime.InteropServices;

namespace StrataLint.Engine;

// Reads repository files straight from the working directory, without git. A
// path names a file or a directory; a directory contributes every file under
// it. While walking a directory, names that start with a dot are skipped with
// everything beneath them: they are tool caches and OS metadata, not repository
// content. A path named explicitly is read whatever its name.
internal static class WorkingTreeReader
{
    internal static RawRepositorySnapshot Read(string repositoryRoot, IReadOnlyList<string> paths)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(paths);
        var root = Path.GetFullPath(repositoryRoot);
        var files = new SortedSet<string>(StringComparer.Ordinal);
        foreach (var path in paths)
        {
            if (!RepoPath.TryCreate(path, out _))
            {
                throw new ArgumentException($"not a repository path: {path}", nameof(paths));
            }

            var full = FullPath(root, path);
            if (File.Exists(full))
            {
                files.Add(path);
            }
            else if (Directory.Exists(full))
            {
                Collect(root, full, files);
            }
        }

        var ordered = files.ToArray();
        var entries = new RawRepositoryEntry[ordered.Length];
        Parallel.For(0, ordered.Length, index => entries[index] = new RawRepositoryEntry(
            ordered[index],
            ImmutableCollectionsMarshal.AsImmutableArray(File.ReadAllBytes(FullPath(root, ordered[index])))));
        return RawRepositorySnapshot.Create(entries);
    }

    private static void Collect(string root, string directory, SortedSet<string> files)
    {
        var pending = new Stack<string>();
        pending.Push(directory);
        while (pending.TryPop(out var current))
        {
            foreach (var file in Directory.EnumerateFiles(current))
            {
                if (!IsDotName(file))
                {
                    files.Add(Path.GetRelativePath(root, file).Replace(Path.DirectorySeparatorChar, '/'));
                }
            }

            foreach (var child in Directory.EnumerateDirectories(current))
            {
                // A linked directory is not walked, so a link cannot form a cycle.
                if (!IsDotName(child) && (File.GetAttributes(child) & FileAttributes.ReparsePoint) == 0)
                {
                    pending.Push(child);
                }
            }
        }
    }

    private static bool IsDotName(string path) => Path.GetFileName(path).StartsWith('.');

    private static string FullPath(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));
}
