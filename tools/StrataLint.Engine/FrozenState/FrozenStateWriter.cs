using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static class FrozenStateWriter
{
    internal static bool Write(string root, RepoPath modulePath, StatementId statementId)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(root);
        ArgumentNullException.ThrowIfNull(modulePath);
        ArgumentNullException.ThrowIfNull(statementId);
        var bytes = FrozenStateRecord.Encode(statementId);
        var path = AbsolutePath(root, modulePath);
        if (File.Exists(path) && File.ReadAllBytes(path).AsSpan().SequenceEqual(bytes.AsSpan()))
        {
            return false;
        }

        ReplaceAtomically(path, bytes.AsSpan());
        return true;
    }

    internal static bool Delete(string root, RepoPath modulePath)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(root);
        ArgumentNullException.ThrowIfNull(modulePath);
        var path = AbsolutePath(root, modulePath);
        if (!File.Exists(path))
        {
            return false;
        }

        File.Delete(path);
        return true;
    }

    internal static ImmutableArray<byte>? ReadCurrentBytes(string root, RepoPath modulePath)
    {
        var path = AbsolutePath(root, modulePath);
        return File.Exists(path)
            ? ImmutableArray.CreateRange(File.ReadAllBytes(path))
            : null;
    }

    internal static void Restore(
        string root,
        RepoPath modulePath,
        ImmutableArray<byte>? previousBytes)
    {
        var path = AbsolutePath(root, modulePath);
        if (previousBytes is null)
        {
            File.Delete(path);
            return;
        }

        ReplaceAtomically(path, previousBytes.Value.AsSpan());
    }

    private static string AbsolutePath(string root, RepoPath modulePath)
    {
        var relative = FrozenStatePath.FromModulePath(modulePath).Value
            .Replace('/', Path.DirectorySeparatorChar);
        var fullRoot = Path.GetFullPath(root);
        var path = Path.GetFullPath(Path.Combine(fullRoot, relative));
        var rootedPrefix = fullRoot.TrimEnd(Path.DirectorySeparatorChar)
            + Path.DirectorySeparatorChar;
        if (!path.StartsWith(rootedPrefix, StringComparison.Ordinal))
        {
            throw new ArgumentException("Frozen state path resolves outside the repository root.", nameof(root));
        }

        return path;
    }

    private static void ReplaceAtomically(string path, ReadOnlySpan<byte> bytes)
    {
        var directory = Path.GetDirectoryName(path)
            ?? throw new InvalidOperationException("Frozen state path has no parent directory.");
        Directory.CreateDirectory(directory);
        var temporary = Path.Combine(
            directory,
            $".{Path.GetFileName(path)}.{Path.GetRandomFileName()}.tmp");
        try
        {
            using (var stream = new FileStream(
                temporary,
                FileMode.CreateNew,
                FileAccess.Write,
                FileShare.None))
            {
                stream.Write(bytes);
                stream.Flush(flushToDisk: true);
            }

            File.Move(temporary, path, overwrite: true);
        }
        finally
        {
            File.Delete(temporary);
        }
    }
}
