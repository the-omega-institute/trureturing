using System.Collections.Immutable;
using System.Text.Json;

namespace StrataLint.Scribe;

internal sealed record ScribeDefinitionSelection(
    ImmutableArray<string> Paths,
    string? Failure)
{
    internal bool IsSuccess => Failure is null;
}

/// <summary>Maps a changed-path manifest to the definitions whose files must run.</summary>
internal static class ScribeDefinitionSelector
{
    internal static ScribeDefinitionSelection Select(string repositoryRoot, IEnumerable<string> changedPaths)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(changedPaths);
        var root = Path.GetFullPath(repositoryRoot);
        var changes = changedPaths
            .Select(Normalize)
            .Where(static path => path is not null)
            .Select(static path => path!)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var sourceRoot = Path.Combine(root, "Blueprint");
        var allSources = Directory.Exists(sourceRoot)
            ? Directory.EnumerateFiles(sourceRoot, "*.scribe.cs", SearchOption.AllDirectories)
                .Select(path => Path.GetRelativePath(root, path).Replace('\\', '/'))
                .ToImmutableArray()
            : ImmutableArray<string>.Empty;
        var selected = new HashSet<string>(StringComparer.Ordinal);

        foreach (var change in changes)
        {
            if (change.EndsWith(".scribe.cs", StringComparison.Ordinal)
                && change.StartsWith("Blueprint/", StringComparison.Ordinal)
                && File.Exists(Path.Combine(root, change.Replace('/', Path.DirectorySeparatorChar))))
            {
                selected.Add(change);
            }

            if (change.StartsWith("D5/", StringComparison.Ordinal)
                && change.EndsWith(".lean", StringComparison.Ordinal))
            {
                AddIfPresent(root, selected, "Blueprint/" + change[..^5] + ".scribe.cs");
            }

            if (change.StartsWith("Golden/Projection/", StringComparison.Ordinal)
                && change.EndsWith(".json", StringComparison.Ordinal))
            {
                var projectionFailure = AddProjectionRecords(root, selected, change);
                if (projectionFailure is not null)
                    return new([], projectionFailure);
            }
        }

        var sharedChanges = changes
            .Where(path => path.StartsWith("Blueprint/", StringComparison.Ordinal))
            .ToHashSet(StringComparer.Ordinal);
        if (sharedChanges.Count != 0)
        {
            foreach (var source in allSources)
            {
                var declaredSources = ScribeScriptHost.ReadSharedSourcePaths(root, source);
                foreach (var shared in sharedChanges)
                {
                    if (declaredSources.Contains(shared, StringComparer.Ordinal))
                    {
                        selected.Add(source);
                        break;
                    }
                }
            }
        }

        return new(selected.Order(StringComparer.Ordinal).ToImmutableArray(), null);
    }

    private static string? AddProjectionRecords(string root, ISet<string> selected, string relativePath)
    {
        var full = Path.Combine(root, relativePath.Replace('/', Path.DirectorySeparatorChar));
        if (!File.Exists(full))
            return $"projection manifest is missing: {relativePath}";
        try
        {
            using var json = JsonDocument.Parse(File.ReadAllBytes(full));
            if (!json.RootElement.TryGetProperty("declarations", out var declarations)
                || declarations.ValueKind != JsonValueKind.Array)
                return $"projection manifest has no declarations array: {relativePath}";
            foreach (var declaration in declarations.EnumerateArray())
            {
                if (!declaration.TryGetProperty("source_path", out var source)
                    || source.ValueKind != JsonValueKind.String)
                    return $"projection record has no source_path: {relativePath}";
                var lean = source.GetString()?.Replace('\\', '/');
                if (lean is null || !lean.StartsWith("D5/", StringComparison.Ordinal)
                    || !lean.EndsWith(".lean", StringComparison.Ordinal))
                    return $"projection record has invalid source_path: {relativePath}";
                AddIfPresent(root, selected, "Blueprint/" + lean[..^5] + ".scribe.cs");
            }
            return null;
        }
        catch (JsonException exception)
        {
            return $"projection manifest is invalid: {relativePath}: {exception.Message}";
        }
    }

    private static void AddIfPresent(string root, ISet<string> selected, string path)
    {
        if (File.Exists(Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar))))
            selected.Add(path);
    }

    private static string? Normalize(string? value)
    {
        if (string.IsNullOrWhiteSpace(value)) return null;
        var path = value.Replace('\\', '/').Trim();
        return path.StartsWith("./", StringComparison.Ordinal) ? path[2..] : path;
    }
}
