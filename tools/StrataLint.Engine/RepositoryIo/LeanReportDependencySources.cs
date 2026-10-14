using System.Text.Json;
using System.Text.Json.Serialization;

namespace StrataLint.Engine;

internal static class LeanReportDependencySources
{
    private sealed record Include(string Pattern, bool Optional);
    private sealed record PathSet(Include[] Include, string[] Exclude);
    private static readonly JsonSerializerOptions Options = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        AllowDuplicateProperties = false,
        RespectRequiredConstructorParameters = true,
    };

    internal static IEnumerable<RepoPath> Select(RepositorySnapshot snapshot)
    {
        if (!snapshot.TryGetFile(ReportProducerScope.InputManifest, out var file)) return [];
        try
        {
            var manifest = JsonSerializer.Deserialize<JsonElement>(file.Text, Options);
            if (!manifest.TryGetProperty("dependency_sources", out var element)) return [];
            var set = element.Deserialize<PathSet>(Options);
            if (set?.Include is null || set.Exclude is null)
                throw new InvalidDataException("invalid dependency_sources path set");
            var exclude = set.Exclude.Select(FileMapGlob.Create).ToArray();
            var selected = new HashSet<RepoPath>();
            foreach (var include in set.Include)
            {
                if (include is null) throw new InvalidDataException("invalid dependency_sources include");
                var glob = FileMapGlob.Create(include.Pattern);
                var matches = snapshot.Files.Keys.Where(path => glob.IsMatch(path.Value)
                    && !exclude.Any(item => item.IsMatch(path.Value))).ToArray();
                if (!include.Optional && matches.Length == 0)
                    throw new InvalidDataException("required dependency_sources registration has no files: " + include.Pattern);
                foreach (var path in matches)
                {
                    if (!path.Value.EndsWith(".lean", StringComparison.Ordinal)
                        || snapshot.Files[path].RawBytes.IsDefault)
                        throw new InvalidDataException("dependency_sources must contain readable Lean source: " + path.Value);
                    selected.Add(path);
                }
            }
            return selected;
        }
        catch (Exception exception) when (exception is JsonException or FormatException or InvalidOperationException)
        {
            throw new InvalidDataException("invalid " + ReportProducerScope.InputManifest
                + " dependency_sources: " + exception.Message, exception);
        }
    }
}
