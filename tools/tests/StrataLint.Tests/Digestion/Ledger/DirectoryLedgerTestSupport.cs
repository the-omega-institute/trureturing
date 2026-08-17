using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class DirectoryLedgerTestSupport
{
    internal static Dictionary<string, string> Project(IReadOnlyDictionary<string, string> files)
    {
        var raw = RawRepositorySnapshot.Create(files.Select(static pair =>
            RawRepositoryEntry.FromText(pair.Key, pair.Value)));
        var snapshot = Assert.IsType<SnapshotDecodeOutcome.Decoded>(
            SnapshotDecoder.Decode(raw)).Snapshot;
        var ledger = BackfillInventoryLoader.Load(snapshot);
        var result = new Dictionary<string, string>(files, StringComparer.Ordinal);
        RemoveLedger(result);
        foreach (var source in ledger.RequireDigestionSources())
        {
            result[$"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml"] =
                Encoding.UTF8.GetString(BackfillInventoryWriter.WriteSourceMetadata(source).AsSpan());
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

    internal static void ReplaceWithProjection(
        IDictionary<string, string> files,
        string ledger)
    {
        var projected = Project(new Dictionary<string, string>(StringComparer.Ordinal)
        {
            [BackfillInventoryLoader.RelativePath] = ledger,
        });
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
