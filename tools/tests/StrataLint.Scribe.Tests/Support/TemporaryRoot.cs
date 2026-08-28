namespace StrataLint.Scribe.Tests;

/// <summary>
/// A throwaway repository root. Tests judge a tree they built, never the live one: a
/// production reader handed the repository root is what the harness counts as an
/// unresolvable repository read.
/// </summary>
internal sealed class TemporaryRoot : IDisposable
{
    internal TemporaryRoot()
    {
        Path = System.IO.Path.Combine(
            System.IO.Path.GetTempPath(),
            "stratalint-scribe-root-" + Guid.NewGuid().ToString("N"));
        TemporaryFileSystem.Directory.CreateDirectory(Path);
    }

    internal string Path { get; }

    internal string Resolve(string relativePath)
    {
        var full = System.IO.Path.Combine(Path, relativePath.Replace('/', System.IO.Path.DirectorySeparatorChar));
        TemporaryFileSystem.Directory.CreateDirectory(System.IO.Path.GetDirectoryName(full)!);
        return full;
    }

    public void Dispose() => TemporaryFileSystem.Directory.Delete(Path, recursive: true);
}
