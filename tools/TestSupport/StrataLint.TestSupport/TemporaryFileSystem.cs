using System.Text;

namespace StrataLint.TestSupport;

// Every path-bearing operation is confined to the process temporary directory.
public static class TemporaryFileSystem
{
    public static class File
    {
        public static bool Exists(string path) => System.IO.File.Exists(EnsureTemporaryPath(path));
        public static string ReadAllText(string path) =>
            System.IO.File.ReadAllText(EnsureTemporaryPath(path));
        public static string ReadAllText(string path, Encoding encoding) =>
            System.IO.File.ReadAllText(EnsureTemporaryPath(path), encoding);
        public static byte[] ReadAllBytes(string path) =>
            System.IO.File.ReadAllBytes(EnsureTemporaryPath(path));
        public static void WriteAllText(string path, string contents) =>
            System.IO.File.WriteAllText(EnsureTemporaryPath(path), contents);
        public static void WriteAllText(string path, string contents, Encoding encoding) =>
            System.IO.File.WriteAllText(EnsureTemporaryPath(path), contents, encoding);
        public static void WriteAllBytes(string path, byte[] contents) =>
            System.IO.File.WriteAllBytes(EnsureTemporaryPath(path), contents);
        public static void AppendAllText(string path, string contents) =>
            System.IO.File.AppendAllText(EnsureTemporaryPath(path), contents);
        public static void AppendAllText(string path, string contents, Encoding encoding) =>
            System.IO.File.AppendAllText(EnsureTemporaryPath(path), contents, encoding);
        public static void Delete(string path) =>
            System.IO.File.Delete(EnsureTemporaryPath(path));
    }

    public static class Directory
    {
        public static bool Exists(string path) =>
            System.IO.Directory.Exists(EnsureTemporaryPath(path));
        public static DirectoryInfo CreateDirectory(string path) =>
            System.IO.Directory.CreateDirectory(EnsureTemporaryPath(path));
        public static DirectoryInfo CreateTempSubdirectory(string? prefix = null) =>
            System.IO.Directory.CreateTempSubdirectory(prefix);
        public static string GetCurrentDirectory() => System.IO.Directory.GetCurrentDirectory();
        public static void Delete(string path, bool recursive) =>
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
