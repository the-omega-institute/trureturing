using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionIngestor
{
    /// <summary>
    /// Registers eligible canonical regular Markdown inputs with generic-v1 and a
    /// source id derived from the file stem. FILEMAP owns source eligibility.
    /// </summary>
    internal static BackfillInventoryDocument RegisterDefaultTheorySources(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        ImmutableHashSet<string>? registrationPaths = null)
    {
        var sources = document.RequireDigestionSources();
        var declaredPaths = sources
            .Select(static source => source.SourcePath)
            .ToHashSet(StringComparer.Ordinal);
        var sourcePathsById = sources.ToDictionary(
            static source => source.SourceId,
            static source => source.SourcePath,
            StringComparer.Ordinal);
        var registered = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        var manifest = snapshot.TryGetFile(FileMapLoader.RelativePath, out _)
            ? FileMapLoader.LoadSnapshot(snapshot) : null;
        foreach (var path in snapshot.Files.Keys
                     .Select(static path => path.Value)
                     .Where(static path => path.StartsWith(
                         DigestionOpaquePathPolicy.TheoryRootPath,
                         StringComparison.Ordinal))
                     .Where(path => path.EndsWith(".md", StringComparison.Ordinal)
                         && DigestionSourceEligibility.IsEligible(snapshot, path, manifest))
                     .Where(path => !declaredPaths.Contains(path))
                     .Where(path => registrationPaths is null || registrationPaths.Contains(path))
                     .Order(StringComparer.Ordinal))
        {
            var sourceId = DeriveSourceId(path);
            if (sourcePathsById.TryGetValue(sourceId, out var claimant))
            {
                throw new FormatException(
                    $"theory source id derived from {path} collides with {claimant}: {sourceId}");
            }

            sourcePathsById.Add(sourceId, path);
            registered.Add(new DigestionLedgerSource(
                sourceId,
                path,
                AtomizerRegistry.GenericId,
                [],
                GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
                ImmutableArray<DigestionLedgerEntry>.Empty));
        }

        return registered.Count == 0
            ? document
            : document.WithDigestionSources(sources.AddRange(registered));
    }

    /// <summary>
    /// Derives a lowercase source id from the file stem, collapsing runs of
    /// non-alphanumeric characters to a dash.
    /// </summary>
    internal static string DeriveSourceId(string path)
    {
        var stem = Path.GetFileNameWithoutExtension(path);
        var id = new string(stem.Select(static character =>
            char.IsAsciiLetterOrDigit(character) ? char.ToLowerInvariant(character) : '-').ToArray());
        id = string.Join('-', id.Split('-', StringSplitOptions.RemoveEmptyEntries));
        return id.Length > 0 ? id : "source-" + DigestionFingerprint.ShortHash(path);
    }
}

internal static class DigestionSourceConflictMarkers
{
    internal const string DiagnosticCode = "INGEST-CONFLICT-MARKER-001";

    internal static int? FindFirstLine(ReadOnlySpan<byte> bytes)
    {
        var start = bytes.Length >= 3
            && bytes[0] == 0xef
            && bytes[1] == 0xbb
            && bytes[2] == 0xbf
                ? 3
                : 0;
        var lineNumber = 1;
        while (true)
        {
            var end = start;
            while (end < bytes.Length
                && bytes[end] != (byte)'\r'
                && bytes[end] != (byte)'\n')
            {
                end++;
            }

            var line = bytes[start..end];
            if (line.StartsWith("<<<<<<< "u8)
                || line.StartsWith("||||||| "u8)
                || line.SequenceEqual("======="u8)
                || line.StartsWith(">>>>>>> "u8))
            {
                return lineNumber;
            }

            if (end == bytes.Length)
            {
                return null;
            }

            if (bytes[end] == (byte)'\r'
                && end + 1 < bytes.Length
                && bytes[end + 1] == (byte)'\n')
            {
                end++;
            }

            start = end + 1;
            lineNumber++;
        }
    }

    internal static string FormatFinding(string sourcePath, int line) =>
        $"{DiagnosticCode} {sourcePath}:{line}: unresolved merge conflict marker in digestion source";
}
