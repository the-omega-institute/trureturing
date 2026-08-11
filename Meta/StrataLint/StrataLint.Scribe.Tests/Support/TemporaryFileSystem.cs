using System.Text;

namespace StrataLint.Scribe.Tests;

// Every path-bearing operation is confined to the process temporary directory.
internal static class TemporaryFileSystem
{
    internal static class File
    {
        internal static bool Exists(string path) => System.IO.File.Exists(EnsureTemporaryPath(path));
        internal static string ReadAllText(string path) =>
            System.IO.File.ReadAllText(EnsureTemporaryPath(path));
        internal static string ReadAllText(string path, Encoding encoding) =>
            System.IO.File.ReadAllText(EnsureTemporaryPath(path), encoding);
        internal static byte[] ReadAllBytes(string path) =>
            System.IO.File.ReadAllBytes(EnsureTemporaryPath(path));
        internal static void WriteAllText(string path, string contents) =>
            System.IO.File.WriteAllText(EnsureTemporaryPath(path), contents);
        internal static void WriteAllText(string path, string contents, Encoding encoding) =>
            System.IO.File.WriteAllText(EnsureTemporaryPath(path), contents, encoding);
        internal static void WriteAllBytes(string path, byte[] contents) =>
            System.IO.File.WriteAllBytes(EnsureTemporaryPath(path), contents);
        internal static void AppendAllText(string path, string contents) =>
            System.IO.File.AppendAllText(EnsureTemporaryPath(path), contents);
        internal static void AppendAllText(string path, string contents, Encoding encoding) =>
            System.IO.File.AppendAllText(EnsureTemporaryPath(path), contents, encoding);
        internal static void Delete(string path) =>
            System.IO.File.Delete(EnsureTemporaryPath(path));
    }

    internal static class Directory
    {
        internal static bool Exists(string path) =>
            System.IO.Directory.Exists(EnsureTemporaryPath(path));
        internal static DirectoryInfo CreateDirectory(string path) =>
            System.IO.Directory.CreateDirectory(EnsureTemporaryPath(path));
        internal static DirectoryInfo CreateTempSubdirectory(string? prefix = null) =>
            System.IO.Directory.CreateTempSubdirectory(prefix);
        internal static string GetCurrentDirectory() => System.IO.Directory.GetCurrentDirectory();
        internal static void Delete(string path, bool recursive) =>
            System.IO.Directory.Delete(EnsureTemporaryPath(path), recursive);
    }

    private static string EnsureTemporaryPath(string path)
    {
        var fullPath = Path.GetFullPath(path);
        var temporaryRoot = Path.TrimEndingDirectorySeparator(Path.GetFullPath(Path.GetTempPath()));
        if (!string.Equals(fullPath, temporaryRoot, StringComparison.Ordinal)
            && !fullPath.StartsWith(temporaryRoot + Path.DirectorySeparatorChar, StringComparison.Ordinal))
        {
            throw new ArgumentException("synthetic fixture path must remain under the temporary directory", nameof(path));
        }

        return fullPath;
    }
}
