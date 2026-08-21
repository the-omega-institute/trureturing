using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal static class GitRepositorySnapshotReader
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static RawRepositorySnapshot ReadCurrent(string repositoryRoot)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        var root = Path.GetFullPath(repositoryRoot);
        var tracked = ParseIndex(Git(root, "ls-files", "--stage", "-z"));
        var paths = tracked.Keys
            .Concat(ParseNulStrings(Git(
                root,
                "ls-files",
                "--others",
                "--exclude-standard",
                "-z")))
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal);
        var entries = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        foreach (var path in paths)
        {
            if (RepositoryPathPolicy.IsUngovernedAgentConfig(path))
            {
                continue;
            }

            if (!RepoPath.TryCreate(path, out _))
            {
                throw new InvalidOperationException($"git emitted an invalid repository path: {path}");
            }

            if (tracked.TryGetValue(path, out var mode) && mode is not ("100644" or "100755"))
            {
                throw new InvalidOperationException(
                    $"non-regular repository entry {path} has git mode {mode}");
            }

            var fullPath = Path.Combine(root, path);
            var info = new FileInfo(fullPath);
            if (!info.Exists)
            {
                continue;
            }

            if (info.LinkTarget is not null || (info.Attributes & FileAttributes.ReparsePoint) != 0)
            {
                throw new InvalidOperationException(
                    $"non-regular repository entry {path} is not a plain file");
            }

            entries.Add(new RawRepositoryEntry(
                path,
                ImmutableArray.CreateRange(File.ReadAllBytes(fullPath))));
        }

        return RawRepositorySnapshot.Create(entries);
    }

    private static byte[] Git(string root, params string[] arguments)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            arguments,
            root,
            TimeSpan.FromSeconds(120),
            64 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                StrictUtf8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                    ? error
                    : "git command failed");
        }

        return result.StandardOutput;
    }

    private static Dictionary<string, string> ParseIndex(byte[] bytes)
    {
        var result = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var entry in SplitNul(bytes))
        {
            var tab = Array.IndexOf(entry, (byte)'\t');
            if (tab <= 0)
            {
                throw new InvalidOperationException("git index emitted invalid metadata");
            }

            var metadata = StrictUtf8.GetString(entry.AsSpan(0, tab)).Split(' ');
            var path = StrictUtf8.GetString(entry.AsSpan(tab + 1));
            if (metadata.Length != 3 || metadata[2] != "0" || !result.TryAdd(path, metadata[0]))
            {
                throw new InvalidOperationException(
                    $"unmerged or duplicate repository entry: {path}");
            }
        }

        return result;
    }

    private static IEnumerable<string> ParseNulStrings(byte[] bytes) =>
        SplitNul(bytes).Select(static item => StrictUtf8.GetString(item));

    private static IEnumerable<byte[]> SplitNul(byte[] bytes)
    {
        var start = 0;
        for (var index = 0; index <= bytes.Length; index++)
        {
            if (index != bytes.Length && bytes[index] != 0)
            {
                continue;
            }

            if (index > start)
            {
                yield return bytes[start..index];
            }

            start = index + 1;
        }
    }
}
