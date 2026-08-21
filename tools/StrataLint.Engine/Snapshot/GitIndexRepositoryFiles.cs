using System.Text;

namespace StrataLint.Engine;

internal static class GitIndexRepositoryFiles
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static IReadOnlyList<(string RelativePath, string FullPath)> Enumerate(
        string repositoryRoot) => EnumerateTracked(repositoryRoot)
        .Select(entry => (
            RelativePath: entry.RelativePath,
            FullPath: Path.Combine(
                repositoryRoot,
                entry.RelativePath.Replace('/', Path.DirectorySeparatorChar))))
        .Where(static file => File.Exists(file.FullPath))
        .ToArray();

    internal static IReadOnlyList<(string RelativePath, string Mode)> EnumerateTracked(
        string repositoryRoot)
    {
        var result = BoundedProcessRunner.Run(
            "git",
            ["ls-files", "--stage", "-z"],
            repositoryRoot,
            TimeSpan.FromSeconds(120),
            64 * 1024 * 1024);
        if (result.ExitCode != 0)
        {
            throw new InvalidOperationException(
                StrictUtf8.GetString(result.StandardError).Trim() is { Length: > 0 } error
                    ? error
                    : "git ls-files --stage failed");
        }

        var paths = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var entry in SplitNul(result.StandardOutput))
        {
            var tab = Array.IndexOf(entry, (byte)'\t');
            if (tab <= 0)
            {
                throw new InvalidOperationException("git index emitted invalid metadata");
            }

            var metadata = StrictUtf8.GetString(entry.AsSpan(0, tab)).Split(' ');
            var path = StrictUtf8.GetString(entry.AsSpan(tab + 1));
            if (metadata.Length != 3 || metadata[2] != "0" || !paths.TryAdd(path, metadata[0]))
            {
                throw new InvalidOperationException(
                    $"unmerged or duplicate repository entry: {path}");
            }
        }

        return paths
            .Where(static pair => !RepositoryPathPolicy.IsUngovernedAgentConfig(pair.Key))
            .OrderBy(static pair => pair.Key, StringComparer.Ordinal)
            .Select(static pair => (RelativePath: pair.Key, Mode: pair.Value))
            .ToArray();
    }

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
