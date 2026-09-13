using StrataLint.Engine;
using System.IO.Compression;

namespace StrataLint.Cli;

internal static class LeanSourceContextArtifact
{
    internal static LeanSourceContextInput ReadBundle(string report, RepositorySnapshot current,
        RepositorySnapshot? protectedBase) => ReadBytes(report) is { } bytes
        ? LeanSourceContextInput.Load(bytes, current, protectedBase) : LeanSourceContextInput.Empty;

    private static byte[]? ReadBytes(string report)
    {
        if (File.Exists(report + ".source-context.json"))
            return File.ReadAllBytes(report + ".source-context.json");
        var path = RawLeanReportArtifact.MaterialsPath(report);
        if (!File.Exists(path)) return null;
        using var archive = ZipFile.OpenRead(path);
        var entries = archive.Entries.Where(entry => entry.FullName == LeanSourceContextInput.ArchiveEntryName).ToArray();
        if (entries.Length > 1) throw new InvalidDataException("duplicate source context in " + path);
        if (entries.Length == 0) return null;
        using var source = entries[0].Open();
        using var bytes = new MemoryStream();
        source.CopyTo(bytes);
        return bytes.ToArray();
    }
}
