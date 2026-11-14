using System.Text;
using System.Text.RegularExpressions;
using StrataLint.Engine;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static partial class RetireSourcesCommand
{
    // Read raw reverse references without interpreting unrelated settlement records.
    private static RawRepositorySnapshot RequireNoReferences(IRepositoryGateway repository, RepositorySnapshot snapshot,
        string[] removedPrefixes, HashSet<string> removedIds, string[] sourcePaths, string[] archivePaths)
    {
        var sourceTargets = sourcePaths.Select(Path.GetFullPath).ToHashSet(StringComparer.Ordinal);
        var ledgerTargets = removedPrefixes.Select(prefix => Path.GetFullPath(prefix.TrimEnd('/'))).ToArray();
        foreach (var link in FileMapLoader.LoadSnapshot(snapshot).Entries.Select(entry => entry.Symlink).OfType<FileMapSymlink>())
            if ((sourcePaths.Any(source => source == link.ResolvedTarget
                    || link.Kind == "directory" && source.StartsWith(link.ResolvedTarget + "/", StringComparison.Ordinal))
                    || removedPrefixes.Any(prefix => link.ResolvedTarget.StartsWith(prefix, StringComparison.Ordinal)
                        || link.Kind == "directory" && (prefix.TrimEnd('/') == link.ResolvedTarget
                            || prefix.StartsWith(link.ResolvedTarget + "/", StringComparison.Ordinal))))
                && repository.SearchCurrentPaths([DigestionQuerySelection.Literal(link.Path)]).Count > 0)
                throw new FormatException($"SOURCE_SYMLINK_REFERENCED path={link.Path} target={link.ResolvedTarget}");
        var paths = repository.SearchCurrentPaths([BackfillInventoryLoader.RootPath.TrimEnd('/'), ":(glob)**/*.md", ":(glob)**/*.lean"])
            .Where(path => !removedPrefixes.Any(prefix => path.StartsWith(prefix, StringComparison.Ordinal))
                && !sourcePaths.Contains(path, StringComparer.Ordinal)
                && !archivePaths.Contains(path, StringComparer.Ordinal)
                && (path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                    || path.EndsWith(".md", StringComparison.Ordinal) || path.EndsWith(".lean", StringComparison.Ordinal)))
            .Order(StringComparer.Ordinal).ToArray();
        var captured = repository.ReadCurrent(paths.Select(DigestionQuerySelection.Literal).ToArray());
        var requested = paths.ToHashSet(StringComparer.Ordinal);
        foreach (var entry in captured.Entries.Where(entry => requested.Contains(entry.Path)))
        {
            var text = Encoding.UTF8.GetString(entry.Bytes.AsSpan());
            if (entry.Path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal))
            {
                if (entry.Path.EndsWith("/source.toml", StringComparison.Ordinal)
                    && sourcePaths.Any(source => text.Contains(source, StringComparison.Ordinal)))
                    throw new FormatException($"SOURCE_REFERENCED path={entry.Path}");
                if (!removedIds.Contains(Path.GetFileNameWithoutExtension(entry.Path))
                    && !Regex.Matches(text, "[0-9a-f]{64}", RegexOptions.CultureInvariant)
                        .Any(match => removedIds.Contains(match.Value))) continue;
                foreach (var id in AtomReferences(entry.Path, entry.Bytes, text))
                    if (removedIds.Contains(id))
                        throw new FormatException($"ATOM_REFERENCED atom_id={id} path={entry.Path}");
            }
            else
            {
                foreach (Match match in Regex.Matches(text, "atom:(?<id>[0-9a-f]{64})", RegexOptions.CultureInvariant))
                    if (removedIds.Contains(match.Groups["id"].Value))
                        throw new FormatException($"ATOM_REFERENCED atom_id={match.Groups["id"].Value} path={entry.Path}");
                if (entry.Path.EndsWith(".md", StringComparison.Ordinal))
                    foreach (var (url, _, _) in MarkdownLinkSpans.Read(text))
                    {
                        if (string.IsNullOrEmpty(url) || url.StartsWith('#')) continue;
                        var end = url.IndexOfAny(['?', '#']);
                        var path = Uri.UnescapeDataString(end < 0 ? url : url[..end]);
                        if (path.Length == 0) continue;
                        string target;
                        try
                        {
                            if (path.StartsWith('/')) target = Path.GetFullPath(path.TrimStart('/'));
                            else if (Uri.TryCreate(url, UriKind.Absolute, out _)) continue;
                            else target = Path.GetFullPath(path, Path.GetDirectoryName(Path.GetFullPath(entry.Path))!);
                        }
                        catch (Exception error) when (error is ArgumentException or NotSupportedException or PathTooLongException) { continue; }
                        if (sourceTargets.Contains(target) || ledgerTargets.Any(root => target == root
                                || target.StartsWith(root + Path.DirectorySeparatorChar, StringComparison.Ordinal)))
                            throw new FormatException($"SOURCE_REFERENCED target={url} path={entry.Path}");
                    }
                foreach (var source in sourcePaths)
                    if (text.Contains(source, StringComparison.Ordinal) || text.Contains(Path.GetFileName(source), StringComparison.Ordinal))
                        throw new FormatException($"SOURCE_REFERENCED source={source} path={entry.Path}");
            }
        }
        return captured;
    }

    private static IEnumerable<string> AtomReferences(string path,
        System.Collections.Immutable.ImmutableArray<byte> bytes, string text)
    {
        if (path.EndsWith("/source.toml", StringComparison.Ordinal)) return [];
        if (DigestionContextPointerStore.IsCanonicalPath(path))
            return DigestionContextPointerStore.ParseVersions(bytes, DigestionQuerySelection.SourceId(path), Path.GetFileNameWithoutExtension(path))
                .SelectMany(index => index.Entries).SelectMany(entry => entry.Occurrences
                    .SelectMany(occurrence => new[] { occurrence.PreviousAtomId, occurrence.NextAtomId }.OfType<string>())
                    .Append(entry.AtomId));
        if (!DigestionQuerySelection.IsAtomPath(path))
            return Regex.Matches(text, "[0-9a-f]{64}", RegexOptions.CultureInvariant).Select(match => match.Value);
        var root = YamlSubsetParser.Parse(text) as Dictionary<string, object?>
            ?? throw new FormatException($"REFERENCE_RECORD_INVALID path={path}");
        var ids = new List<string> { Path.GetFileNameWithoutExtension(path) };
        if (root.GetValueOrDefault("atom_id") is string id) ids.Add(id);
        if (root.GetValueOrDefault("receipts") is Dictionary<string, object?> receipts)
        {
            if (receipts.GetValueOrDefault("chain_atoms") is { } chainValue)
            {
                if (chainValue is not IEnumerable<object?> chain || chain.Any(item => item is not string))
                    throw new FormatException($"REFERENCE_RECORD_INVALID path={path}");
                ids.AddRange(chain.OfType<string>());
            }
            if (receipts.GetValueOrDefault("nonpropositional") is Dictionary<string, object?> receipt)
                ids.AddRange(new[] { receipt.GetValueOrDefault("previous_atom_id"), receipt.GetValueOrDefault("next_atom_id") }.OfType<string>());
        }
        return ids;
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
