using System.Text;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class SyntheticBackfillFixture
{
    internal static Dictionary<string, string> Expand(IReadOnlyDictionary<string, string> files)
    {
        var expanded = new Dictionary<string, string>(files, StringComparer.Ordinal);
        foreach (var path in new[] { BackfillInventoryLoader.RootPath, "Meta/BACKFILL.yaml" })
        {
            if (!expanded.Remove(path, out var legacy)) continue;
            foreach (var entry in BackfillInventoryWriter.WriteDirectory(BackfillInventoryLoader.Load(legacy)))
            {
                expanded[entry.Path] = Encoding.UTF8.GetString(entry.Bytes.AsSpan());
            }
        }
        return expanded;
    }

    internal static void ExpandInPlace(Dictionary<string, string> files)
    {
        var expanded = Expand(files);
        files.Clear();
        foreach (var (path, text) in expanded) files[path] = text;
    }

    internal static string AtomPath(string legacy) =>
        BackfillInventoryWriter.WriteDirectory(BackfillInventoryLoader.Load(legacy))
            .Single(static entry => entry.Path.EndsWith(".yaml", StringComparison.Ordinal)).Path;

    internal static string AtomText(string legacy, string atomId) =>
        Encoding.UTF8.GetString(BackfillInventoryWriter.WriteDirectory(BackfillInventoryLoader.Load(legacy))
            .Single(entry => entry.Path.EndsWith("/" + atomId + ".yaml", StringComparison.Ordinal))
            .Bytes.AsSpan());

    internal static void WriteDirectory(string root, string legacy)
    {
        foreach (var entry in BackfillInventoryWriter.WriteDirectory(BackfillInventoryLoader.Load(legacy)))
        {
            var path = Path.Combine(root, entry.Path.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, entry.Bytes.AsSpan().ToArray());
        }
    }

    internal static string ReadAtom(string root, string atomId)
    {
        var directory = Path.Combine(root,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar));
        var path = Directory.EnumerateFiles(directory, atomId + ".yaml", SearchOption.AllDirectories)
            .Single();
        return File.ReadAllText(path, Encoding.UTF8);
    }
}
