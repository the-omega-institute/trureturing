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
        var root = Path.GetFullPath(repositoryRoot);
        return Select(
            path => File.Exists(FullPath(root, path)) ? File.ReadAllBytes(FullPath(root, path)) : null,
            changedPaths);
    }

    /// <summary>Selects definitions from repository-relative file contents; <c>null</c> marks an absent file.</summary>
    internal static ScribeDefinitionSelection Select(Func<string, byte[]?> readFile, IEnumerable<string> changedPaths)
    {
        ArgumentNullException.ThrowIfNull(readFile);
        ArgumentNullException.ThrowIfNull(changedPaths);
        var changes = changedPaths
            .Select(Normalize)
            .Where(static path => path is not null)
            .Select(static path => path!)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var selected = new HashSet<string>(StringComparer.Ordinal);

        foreach (var change in changes)
        {
            if (change.EndsWith(".scribe.cs", StringComparison.Ordinal)
                && change.StartsWith("Blueprint/", StringComparison.Ordinal)
                && readFile(change) is not null)
            {
                selected.Add(change);
            }

            if (change.StartsWith("D5/", StringComparison.Ordinal)
                && change.EndsWith(".lean", StringComparison.Ordinal))
            {
                AddIfPresent(readFile, selected, "Blueprint/" + change[..^5] + ".scribe.cs");
            }

            if (change.StartsWith("Golden/Projection/", StringComparison.Ordinal)
                && change.EndsWith(".json", StringComparison.Ordinal))
            {
                var projectionFailure = AddProjectionRecords(readFile, selected, change);
                if (projectionFailure is not null)
                    return new([], projectionFailure);
            }
        }

        return new(selected.Order(StringComparer.Ordinal).ToImmutableArray(), null);
    }

    private static string? AddProjectionRecords(
        Func<string, byte[]?> readFile, ISet<string> selected, string relativePath)
    {
        if (readFile(relativePath) is not { } bytes)
            return $"projection manifest is missing: {relativePath}";
        try
        {
            using var json = JsonDocument.Parse(bytes);
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
                AddIfPresent(readFile, selected, "Blueprint/" + lean[..^5] + ".scribe.cs");
            }
            return null;
        }
        catch (JsonException exception)
        {
            return $"projection manifest is invalid: {relativePath}: {exception.Message}";
        }
    }

    private static void AddIfPresent(Func<string, byte[]?> readFile, ISet<string> selected, string path)
    {
        if (readFile(path) is not null)
            selected.Add(path);
    }

    private static string FullPath(string root, string path) =>
        Path.Combine(root, path.Replace('/', Path.DirectorySeparatorChar));

    private static string? Normalize(string? value)
    {
        if (string.IsNullOrWhiteSpace(value)) return null;
        var path = value.Replace('\\', '/').Trim();
        return path.StartsWith("./", StringComparison.Ordinal) ? path[2..] : path;
    }
}
