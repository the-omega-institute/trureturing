using System.Text;

namespace StrataLint.TestSupport;

internal static class TestExecutable
{
    [System.Runtime.Versioning.UnsupportedOSPlatform("windows")]
    internal static void WriteExecutable(string path, string content)
    {
        Directory.CreateDirectory(Path.GetDirectoryName(path)!);
        File.WriteAllText(path, content, new UTF8Encoding(false));
        File.SetUnixFileMode(path, UnixFileMode.UserRead | UnixFileMode.UserWrite | UnixFileMode.UserExecute);
    }
}
