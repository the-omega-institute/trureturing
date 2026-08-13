using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class DirectoryLedgerTestSupport
{
    internal static Dictionary<string, string> Project(IReadOnlyDictionary<string, string> files)
    {
        var ledger = BackfillInventoryLoader.Load(files[BackfillInventoryLoader.RelativePath]);
        var result = new Dictionary<string, string>(files, StringComparer.Ordinal);
        result.Remove(BackfillInventoryLoader.RelativePath);
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

        result[BackfillInventoryLoader.TicketIndexPath] = string.Concat(
            ledger.RequireTickets().Select(static ticket =>
                $"{ticket.CaseId} = \"{ticket.Gid}\"\n"));
        return result;
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
}
