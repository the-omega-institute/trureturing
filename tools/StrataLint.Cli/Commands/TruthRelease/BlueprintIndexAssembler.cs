using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;
using StrataLint.Scribe;
using Trureturing.Truth;

namespace StrataLint.Cli;

internal static class BlueprintIndexAssembler
{
    private const string SourcePrefix = "Blueprint/";
    private const string SourceSuffix = ".scribe.cs";
    private const string ProjectionSuffix = ".md";

    internal static ImmutableArray<byte> Assemble(RepositorySnapshot snapshot)
    {
        ArgumentNullException.ThrowIfNull(snapshot);
        var fileMapFile = RequiredFile(snapshot, FileMapLoader.RelativePath);
        var fileMap = FileMapLoader.Parse(fileMapFile.RawBytes.AsSpan(), FileMapLoader.RelativePath);
        var sources = snapshot.Files.Values
            .Where(static file => file.Path.Value.StartsWith(SourcePrefix, StringComparison.Ordinal)
                && file.Path.Value.EndsWith(SourceSuffix, StringComparison.Ordinal))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToArray();
        if (sources.Length == 0)
        {
            throw new FormatException("immutable revision contains no Blueprint .scribe.cs sources.");
        }

        var sourcePaths = sources.Select(static file => file.Path.Value).ToHashSet(StringComparer.Ordinal);
        var projectionPaths = snapshot.Files.Values
            .Where(static file => file.Path.Value.StartsWith(SourcePrefix, StringComparison.Ordinal)
                && file.Path.Value.EndsWith(ProjectionSuffix, StringComparison.Ordinal))
            .Select(static file => file.Path.Value)
            .ToHashSet(StringComparer.Ordinal);
        var expectedProjectionPaths = sourcePaths
            .Select(static path => path[..^SourceSuffix.Length] + ProjectionSuffix)
            .ToHashSet(StringComparer.Ordinal);
        if (!projectionPaths.SetEquals(expectedProjectionPaths))
        {
            throw new FormatException("Blueprint .scribe.cs sources and .md projections are not paired.");
        }

        var gids = new HashSet<string>(StringComparer.Ordinal);
        var entries = sources.Select(source =>
        {
            var sourcePath = source.Path.Value;
            var projectionPath = sourcePath[..^SourceSuffix.Length] + ProjectionSuffix;
            var gid = sourcePath[SourcePrefix.Length..^SourceSuffix.Length];
            if (!Gid.TryParse(gid, out _) || !gids.Add(gid))
            {
                throw new FormatException($"Blueprint source has invalid or duplicate gid: {gid}");
            }

            var projection = RequiredFile(snapshot, projectionPath);
            return new
            {
                gid,
                source = Artifact(source),
                projection = Artifact(projection),
                filemap = new
                {
                    source = Metadata(UniqueMatch(fileMap, sourcePath)),
                    projection = Metadata(UniqueMatch(fileMap, projectionPath)),
                },
            };
        }).OrderBy(static entry => entry.gid, StringComparer.Ordinal).ToArray();

        var element = JsonSerializer.SerializeToElement(new
        {
            schema = "blueprint-index.v1",
            entries,
        });
        return StructuredCanonicalWriter.WriteJson(element);
    }

    private static object Artifact(RepositoryFile file) => new
    {
        path = file.Path.Value,
        sha256 = "sha256:" + Sha256Sums.HashHex(file.RawBytes.AsSpan()),
    };

    private static object Metadata(FileMapEntry entry) => new
    {
        pattern = entry.Pattern,
        kind = entry.Kind.ToString().ToLowerInvariant(),
        produced_by = entry.ProducedBy,
        consumed_by = entry.ConsumedBy,
        verified_by = entry.VerifiedBy,
        artifact_id = entry.ArtifactId,
        runtime_disposition = entry.RuntimeDisposition,
    };

    private static FileMapEntry UniqueMatch(FileMapManifest fileMap, string path)
    {
        var matches = fileMap.Match(path);
        return matches.Length == 1
            ? matches[0]
            : throw new FormatException(
                $"FILEMAP must classify Blueprint path exactly once: {path} (matches={matches.Length}).");
    }

    private static RepositoryFile RequiredFile(RepositorySnapshot snapshot, string path) =>
        snapshot.TryGetFile(path, out var file)
            ? file
            : throw new FormatException($"immutable revision is missing {path}.");
}
