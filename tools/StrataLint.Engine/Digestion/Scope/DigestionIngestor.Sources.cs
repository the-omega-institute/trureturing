using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class DigestionIngestor
{
    /// <summary>
    /// Every theory document is digested by something. A volume nobody has written a
    /// dialect for used to sit in the tree with no source declaration at all — not refused,
    /// not digested, just unaccounted — because the declaration was a hand-written file and
    /// nothing checked that one existed. It is derivable from the path, so ingest derives
    /// it: the default atomizer, and a source id slugged from the file name. What remains
    /// hand-written is only what is genuinely a decision — that this path is a canonical
    /// volume at all, which stays with <c>governance_documents</c> on the base side.
    /// </summary>
    private static BackfillInventoryDocument RegisterDefaultTheorySources(
        BackfillInventoryDocument document,
        RepositorySnapshot snapshot,
        ImmutableHashSet<string>? registrationPaths = null)
    {
        var sources = document.RequireDigestionSources();
        var declaredPaths = sources
            .Select(static source => source.SourcePath)
            .ToHashSet(StringComparer.Ordinal);
        var sourceIds = sources.ToDictionary(
            static source => source.SourceId,
            static source => source.SourcePath,
            StringComparer.Ordinal);
        var registered = ImmutableArray.CreateBuilder<DigestionLedgerSource>();
        foreach (var path in snapshot.Files.Keys
                     .Select(static path => path.Value)
                     .Where(static path => path.StartsWith(
                         DigestionOpaquePathPolicy.TheoryRootPath,
                         StringComparison.Ordinal))
                     .Where(path => !declaredPaths.Contains(path))
                     .Where(path => registrationPaths is null || registrationPaths.Contains(path))
                     .Order(StringComparer.Ordinal))
        {
            var sourceId = DeriveSourceId(path);
            if (sourceIds.TryGetValue(sourceId, out var claimant))
            {
                throw new FormatException(
                    $"theory source id derived from {path} collides with {claimant}: {sourceId}");
            }

            sourceIds.Add(sourceId, path);
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
    /// The file name, lowercased, with every run of non-alphanumerics collapsed to a dash —
    /// the shape <c>BackfillInventoryRule</c> already requires of a source id.
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
