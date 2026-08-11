using System.Text;

namespace StrataLint.Scribe.Tests;

// Synthetic fixture I/O is intentionally separate from repository access and is not recorded.
internal static class TemporaryFileSystem
{
    internal static class File
    {
        internal static bool Exists(string path) => System.IO.File.Exists(path);
        internal static string ReadAllText(string path) => System.IO.File.ReadAllText(path);
        internal static string ReadAllText(string path, Encoding encoding) =>
            System.IO.File.ReadAllText(path, encoding);
        internal static byte[] ReadAllBytes(string path) => System.IO.File.ReadAllBytes(path);
        internal static void WriteAllText(string path, string contents) =>
            System.IO.File.WriteAllText(path, contents);
        internal static void WriteAllText(string path, string contents, Encoding encoding) =>
            System.IO.File.WriteAllText(path, contents, encoding);
        internal static void WriteAllBytes(string path, byte[] contents) =>
            System.IO.File.WriteAllBytes(path, contents);
        internal static void AppendAllText(string path, string contents) =>
            System.IO.File.AppendAllText(path, contents);
        internal static void AppendAllText(string path, string contents, Encoding encoding) =>
            System.IO.File.AppendAllText(path, contents, encoding);
        internal static void Copy(string source, string destination, bool overwrite = false) =>
            System.IO.File.Copy(source, destination, overwrite);
        internal static void Delete(string path) => System.IO.File.Delete(path);
    }

    internal static class Directory
    {
        internal static bool Exists(string path) => System.IO.Directory.Exists(path);
        internal static DirectoryInfo CreateDirectory(string path) =>
            System.IO.Directory.CreateDirectory(path);
        internal static DirectoryInfo CreateTempSubdirectory(string? prefix = null) =>
            System.IO.Directory.CreateTempSubdirectory(prefix);
        internal static IEnumerable<string> EnumerateFiles(
            string path,
            string searchPattern,
            SearchOption searchOption = SearchOption.TopDirectoryOnly) =>
            System.IO.Directory.EnumerateFiles(path, searchPattern, searchOption);
        internal static string GetCurrentDirectory() => System.IO.Directory.GetCurrentDirectory();
        internal static void Delete(string path, bool recursive) =>
            System.IO.Directory.Delete(path, recursive);
    }
}
