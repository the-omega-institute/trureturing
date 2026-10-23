using System.Runtime.InteropServices;
using System.Security.Cryptography;
using System.Text;
using Microsoft.Win32.SafeHandles;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed class WorktreeInitializationScope : IDisposable
{
    private readonly List<FileStream> handles = [];

    internal static WorktreeInitializationScope Acquire(string source, string path, string branch)
    {
        var physical = LeanCacheGuard.PhysicalPath(path);
        var ancestors = new List<string>();
        for (var parent = Directory.GetParent(physical); parent is not null; parent = parent.Parent)
            ancestors.Add(parent.FullName);
        ancestors.Reverse();
        var keys = ancestors.Select(parent => (Key: "tree:" + parent, Exclusive: false))
            .Concat(new[] { (Key: "tree:" + physical, Exclusive: true),
                (Key: "ref:refs/heads/" + branch, Exclusive: true) });
        return AcquireKeys(source, keys);
    }

    internal static WorktreeInitializationScope AcquireReference(string source, string branch) =>
        AcquireKeys(source, [("ref:refs/heads/" + branch, true)]);

    private static WorktreeInitializationScope AcquireKeys(
        string source, IEnumerable<(string Key, bool Exclusive)> keys)
    {
        if (OperatingSystem.IsWindows())
            throw new PlatformNotSupportedException("cooperative worktree scopes require macOS or Linux");
        var metadata = Path.Combine(source, ".git");
        if (File.Exists(metadata))
        {
            var pointer = File.ReadAllText(metadata).Trim();
            if (!pointer.StartsWith("gitdir: ", StringComparison.Ordinal))
                throw new IOException("invalid Git pointer");
            metadata = Path.GetFullPath(pointer[8..], source);
            metadata = Path.GetFullPath(File.ReadAllText(Path.Combine(metadata, "commondir")).Trim(), metadata);
        }
        if (!Directory.Exists(metadata)) throw new IOException("Git metadata is absent");
        var directory = Path.Combine(metadata, "worktree-operations");
        Directory.CreateDirectory(directory);
        var scope = new WorktreeInitializationScope();
        try
        {
            foreach (var (key, exclusive) in keys)
            {
                var address = Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(key)));
                var stream = new FileStream(Path.Combine(directory, address + ".lock"),
                    FileMode.OpenOrCreate, FileAccess.ReadWrite, FileShare.ReadWrite);
                scope.handles.Add(stream);
                if (Flock(stream.SafeFileHandle, (exclusive ? 2 : 1) | 4) != 0)
                    throw new IOException("worktree initialization scope is busy");
                // Descendant commands retain this open file description across exec.
                if (Fcntl(stream.SafeFileHandle, 2, 0) != 0)
                    throw new IOException("cannot inherit initialization scope");
            }
            return scope;
        }
        catch
        {
            scope.Dispose();
            throw;
        }
    }

    public void Dispose()
    {
        // Close, never LOCK_UN: a surviving descendant may own the same description.
        foreach (var stream in handles) stream.Dispose();
        handles.Clear();
    }

    [DllImport("libc", EntryPoint = "flock", SetLastError = true)]
    private static extern int Flock(SafeFileHandle handle, int operation);

    [DllImport("libc", EntryPoint = "fcntl", SetLastError = true)]
    private static extern int Fcntl(SafeFileHandle handle, int command, int flags);
}
