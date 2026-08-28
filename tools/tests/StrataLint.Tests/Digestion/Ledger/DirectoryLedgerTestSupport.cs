using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class DirectoryLedgerTestSupport
{
    internal static Dictionary<string, string> Project(IReadOnlyDictionary<string, string> files)
    {
        var ledger = BackfillInventoryLoader.Load(Decode(files));
        var result = new Dictionary<string, string>(files, StringComparer.Ordinal);
        RemoveLedger(result);
        foreach (var source in ledger.RequireDigestionSources())
        {
            var projectedSource = source.Atomizer == AtomizerRegistry.NoAtomizerId
                ? source
                : source with
                {
                    GenreRegistryProjection = GenreRegistryProjection.Available(
                        GenreRegistryCheck.Collected([])),
                };
            result[$"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml"] =
                Encoding.UTF8.GetString(BackfillInventoryWriter.WriteSourceMetadata(projectedSource).AsSpan());
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                result[$"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml"] =
                    Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
            }
        }

        return result;
    }

    internal static RawRepositorySnapshot Project(RawRepositorySnapshot snapshot)
    {
        var ledger = BackfillInventoryLoader.Load(Decode(snapshot));
        var entries = snapshot.Entries
            .Where(static entry =>
                !string.Equals(entry.Path, BackfillInventoryLoader.RelativePath, StringComparison.Ordinal)
                && !BackfillInventoryLoader.IsCanonicalPath(entry.Path))
            .ToList();
        foreach (var source in ledger.RequireDigestionSources())
        {
            var projectedSource = source.Atomizer == AtomizerRegistry.NoAtomizerId
                ? source
                : source with
                {
                    GenreRegistryProjection = GenreRegistryProjection.Available(
                        GenreRegistryCheck.Collected([])),
                };
            entries.Add(new RawRepositoryEntry(
                $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(projectedSource)));
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                entries.Add(new RawRepositoryEntry(
                    $"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml",
                    BackfillInventoryWriter.WriteAtom(entry)));
            }
        }

        return RawRepositorySnapshot.Create(entries);
    }

    private static RepositorySnapshot Decode(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        return Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
    }

    private static RepositorySnapshot Decode(RawRepositorySnapshot snapshot) =>
        Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(snapshot)).Snapshot;

    internal static void ReplaceWithProjection(
        IDictionary<string, string> files,
        BackfillInventoryDocument ledger)
    {
        var projected = new Dictionary<string, string>(StringComparer.Ordinal);
        foreach (var source in ledger.RequireDigestionSources())
        {
            projected[$"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml"] =
                Encoding.UTF8.GetString(BackfillInventoryWriter.WriteSourceMetadata(source).AsSpan());
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                projected[$"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml"] =
                    Encoding.UTF8.GetString(BackfillInventoryWriter.WriteAtom(entry).AsSpan());
            }
        }

        RemoveLedger(files);
        foreach (var (path, text) in projected)
        {
            files[path] = text;
        }
    }

    internal static void Write(string repositoryRoot, IReadOnlyDictionary<string, string> files)
    {
        foreach (var (path, text) in files.Where(static pair =>
                     BackfillInventoryLoader.IsCanonicalPath(pair.Key)))
        {
            var outputPath = Path.Combine(
                repositoryRoot,
                path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
            File.WriteAllText(outputPath, text, new UTF8Encoding(false));
        }
    }

    internal static string Image(string repositoryRoot)
    {
        var root = Path.GetFullPath(repositoryRoot);
        var paths = Directory.EnumerateFiles(
                Path.Combine(root, BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)),
                "*",
                SearchOption.AllDirectories)
            .Order(StringComparer.Ordinal);
        return string.Concat(paths.Select(path =>
            Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/')
            + "\0"
            + Convert.ToBase64String(File.ReadAllBytes(path))
            + "\n"));
    }

    internal static string RepositoryImage(string repositoryRoot)
    {
        var root = Path.GetFullPath(repositoryRoot);
        return string.Concat(Directory.EnumerateFiles(root, "*", SearchOption.AllDirectories)
            .Order(StringComparer.Ordinal)
            .Select(path => Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/')
                + "\0"
                + Convert.ToBase64String(File.ReadAllBytes(path))
                + "\n"));
    }

    internal static Dictionary<string, string> OverlayRepositoryFiles(
        string repositoryRoot,
        IReadOnlyDictionary<string, string> files)
    {
        var result = new Dictionary<string, string>(files, StringComparer.Ordinal);
        foreach (var path in Directory.EnumerateFiles(
                     repositoryRoot,
                     "*",
                     SearchOption.AllDirectories))
        {
            var relative = Path.GetRelativePath(repositoryRoot, path)
                .Replace(Path.DirectorySeparatorChar, '/');
            result[relative] = File.ReadAllText(path);
        }

        return result;
    }

    internal static string Image(BackfillInventoryDocument ledger)
    {
        var files = new List<(string Path, byte[] Bytes)>();
        foreach (var source in ledger.RequireDigestionSources())
        {
            files.Add((
                $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml",
                BackfillInventoryWriter.WriteSourceMetadata(source).ToArray()));
            foreach (var entry in source.Entries)
            {
                var state = DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)
                    + "-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                files.Add((
                    $"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml",
                    BackfillInventoryWriter.WriteAtom(entry).ToArray()));
            }
        }

        return string.Concat(files
            .OrderBy(static file => file.Path, StringComparer.Ordinal)
            .Select(static file => file.Path
                + "\0"
                + Convert.ToBase64String(file.Bytes)
                + "\n"));
    }

    private static void RemoveLedger(IDictionary<string, string> files)
    {
        files.Remove(BackfillInventoryLoader.RelativePath);
        foreach (var path in files.Keys
                     .Where(BackfillInventoryLoader.IsCanonicalPath)
                     .ToArray())
        {
            files.Remove(path);
        }
    }
}
