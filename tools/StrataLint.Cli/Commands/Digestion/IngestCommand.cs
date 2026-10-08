using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    internal static BackfillInventoryDocument LoadDocument(RepositorySnapshot snapshot) =>
        BackfillInventoryLoader.LoadForDigestion(snapshot);

    internal static RawRepositorySnapshot ReplaceLedger(
        RawRepositorySnapshot snapshot,
        BackfillInventoryDocument current,
        BackfillInventoryDocument replacement)
    {
        var matches = snapshot.Entries.Count(static entry =>
            entry.Path == BackfillInventoryLoader.RelativePath);
        if (matches > 0)
        {
            throw new InvalidOperationException("ingest does not write legacy digestion ledgers");
        }

        var entries = snapshot.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var currentSources = current.RequireDigestionSources().ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        var replacementSources = replacement.RequireDigestionSources().ToDictionary(
            static source => source.SourceId,
            StringComparer.Ordinal);
        // Adding is how a theory document nobody declared enters the ledger, so it is
        // allowed and writes the source metadata below. The current writer does not
        // remove a source because that would also discard its receipts.
        var removed = currentSources.Keys.Except(replacementSources.Keys, StringComparer.Ordinal).ToArray();
        if (removed.Length > 0)
        {
            throw new InvalidOperationException(
                "ingest cannot remove directory ledger sources: "
                + string.Join(", ", removed.Order(StringComparer.Ordinal)));
        }

        foreach (var (sourceId, replacementSource) in replacementSources)
        {
            if (currentSources.TryGetValue(sourceId, out var currentSource)
                && SourceMetadataEquals(currentSource, replacementSource))
            {
                continue;
            }

            var metadataPath = $"{BackfillInventoryLoader.RootPath}{sourceId}/source.toml";
            entries[metadataPath] = new RawRepositoryEntry(
                metadataPath,
                BackfillInventoryWriter.WriteSourceMetadata(replacementSource));
        }

        var currentEntries = current.RequireDigestionEntries().ToDictionary(
            static entry => (entry.SourceId, entry.AtomId));
        var replacementEntries = replacement.RequireDigestionEntries().ToDictionary(
            static entry => (entry.SourceId, entry.AtomId));
        foreach (var key in currentEntries.Keys.Except(replacementEntries.Keys))
        {
            throw new InvalidOperationException(
                $"ingest cannot remove directory ledger atom {key.AtomId}");
        }

        var atomPaths = ExistingAtomPaths(entries.Keys);
        foreach (var (key, replacementEntry) in replacementEntries)
        {
            if (currentEntries.TryGetValue(key, out var currentEntry))
            {
                var currentBytes = BackfillInventoryWriter.WriteAtom(currentEntry);
                var replacementBytes = BackfillInventoryWriter.WriteAtom(replacementEntry);
                var currentPath = ExistingAtomPath(atomPaths, key.SourceId, key.AtomId);
                var replacementPath = NewAtomPath(replacementEntry);
                if (currentPath == replacementPath
                    && currentBytes.AsSpan().SequenceEqual(replacementBytes.AsSpan()))
                {
                    continue;
                }

                entries.Remove(currentPath);
                if (!entries.TryAdd(
                        replacementPath,
                        new RawRepositoryEntry(replacementPath, replacementBytes)))
                {
                    throw new InvalidOperationException(
                        $"directory ledger atom path already exists: {replacementPath}");
                }

                continue;
            }

            var path = NewAtomPath(replacementEntry);
            if (!entries.TryAdd(
                    path,
                    new RawRepositoryEntry(path, BackfillInventoryWriter.WriteAtom(replacementEntry))))
            {
                throw new InvalidOperationException($"directory ledger atom path already exists: {path}");
            }
        }

        return RawRepositorySnapshot.Create(entries.Values.OrderBy(
            static entry => entry.Path,
            StringComparer.Ordinal));
    }

    private static bool SourceMetadataEquals(
        DigestionLedgerSource current,
        DigestionLedgerSource replacement) =>
        string.Equals(current.SourcePath, replacement.SourcePath, StringComparison.Ordinal)
        && string.Equals(current.Atomizer, replacement.Atomizer, StringComparison.Ordinal)
        && current.GenreRegistryCheck.Kind == replacement.GenreRegistryCheck.Kind
        && current.GenreRegistryCheck.UnregisteredGenres.SequenceEqual(
            replacement.GenreRegistryCheck.UnregisteredGenres,
            StringComparer.Ordinal)
        && current.AcknowledgedStale.SequenceEqual(replacement.AcknowledgedStale);

    // Indexes every ledger path by its source directory and atom file name, so
    // each atom's existing path is one probe instead of a scan of the snapshot.
    private static ILookup<(string SourceId, string AtomId), string> ExistingAtomPaths(
        IEnumerable<string> paths)
    {
        const string extension = ".yaml";
        return paths
            .Where(static path =>
                path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                && path.EndsWith(extension, StringComparison.Ordinal))
            .Select(static path =>
            {
                var sourceEnd = path.IndexOf('/', BackfillInventoryLoader.RootPath.Length);
                var nameStart = path.LastIndexOf('/') + 1;
                return (Path: path, SourceEnd: sourceEnd, NameStart: nameStart);
            })
            .Where(static item => item.SourceEnd >= 0)
            .ToLookup(
                static item => (
                    item.Path[BackfillInventoryLoader.RootPath.Length..item.SourceEnd],
                    item.Path[item.NameStart..^extension.Length]),
                static item => item.Path);
    }

    private static string ExistingAtomPath(
        ILookup<(string SourceId, string AtomId), string> atomPaths,
        string sourceId,
        string atomId)
    {
        var matches = atomPaths[(sourceId, atomId)].ToArray();
        return matches.Length == 1
            ? matches[0]
            : throw new InvalidOperationException(
                $"directory ledger atom {sourceId}/{atomId} does not have exactly one canonical path");
    }
}
