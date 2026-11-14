using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class RetireSourcesCommand
{
    // Read raw reverse references without interpreting unrelated settlement records.
    private static RawRepositorySnapshot RequireNoReferences(IRepositoryGateway repository,
        string[] removedPrefixes, HashSet<string> removedIds, string[] sourcePaths)
    {
        var paths = repository.SearchCurrentPaths([BackfillInventoryLoader.RootPath, "docs", "Blueprint", "Library", "Papers", "Problems", "README.md"])
            .Where(path => !removedPrefixes.Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal))
                && !sourcePaths.Contains(path, StringComparer.Ordinal)
                && (path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                    || path.EndsWith(".md", StringComparison.Ordinal) || path.EndsWith(".lean", StringComparison.Ordinal)))
            .Order(StringComparer.Ordinal).ToArray();
        var captured = repository.ReadCurrent(paths.Select(DigestionQuerySelection.Literal).ToArray());
        foreach (var entry in captured.Entries)
        {
            var text = Encoding.UTF8.GetString(entry.Bytes.AsSpan());
            if (entry.Path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal))
            {
                foreach (Match match in Regex.Matches(text, "[0-9a-f]{64}", RegexOptions.CultureInvariant))
                    if (removedIds.Contains(match.Value))
                        throw new FormatException($"ATOM_REFERENCED atom_id={match.Value} path={entry.Path}");
            }
            else
                foreach (var source in sourcePaths)
                    if (text.Contains(source, StringComparison.Ordinal) || text.Contains(Path.GetFileName(source), StringComparison.Ordinal))
                        throw new FormatException($"SOURCE_REFERENCED source={source} path={entry.Path}");
        }
        return captured;
    }

    private static void RequireSame(RawRepositorySnapshot before, RawRepositorySnapshot after)
    {
        var actual = after.Entries.ToDictionary(entry => entry.Path, StringComparer.Ordinal);
        if (actual.Count != before.Entries.Length || before.Entries.Any(entry =>
                !actual.TryGetValue(entry.Path, out var current) || !current.Bytes.AsSpan().SequenceEqual(entry.Bytes.AsSpan())))
            throw new IOException("INPUT_CHANGED_DURING_RETIREMENT");
    }

    private static void RequireRegularPath(string root, string relative)
    {
        if (!RepoPath.TryCreate(relative, out _)) throw new IOException($"INVALID_PATH path={relative}");
        var current = root;
        foreach (var part in relative.Split('/'))
        {
            current = Path.Combine(current, part);
            var info = new FileInfo(current);
            if (info.LinkTarget is not null || Directory.Exists(current)
                    && new DirectoryInfo(current).LinkTarget is not null)
                throw new IOException($"SYMLINK_PATH path={relative}");
        }
    }
}
