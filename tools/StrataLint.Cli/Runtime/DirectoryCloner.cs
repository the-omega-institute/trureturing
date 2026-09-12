using System.Runtime.InteropServices;
using System.Text;

namespace StrataLint.Cli;

internal sealed record DirectoryCloneResult(
    bool Succeeded,
    int? Errno,
    string? Message);

internal interface IDirectoryCloner
{
    DirectoryCloneResult Clone(string source, string target);
}

/// <summary>
/// Clones a directory tree with one APFS clonefile(2) call, sharing storage blocks
/// while keeping independent files.
/// </summary>
internal sealed class ApfsDirectoryCloner : IDirectoryCloner
{
    internal delegate int CloneFileCall(byte[] source, byte[] target, uint flags);

    private readonly Func<bool> isMacOS;
    private readonly CloneFileCall cloneFile;

    [DllImport("libc", EntryPoint = "clonefile", SetLastError = true)]
    private static extern int NativeCloneFile(byte[] source, byte[] target, uint flags);

    internal ApfsDirectoryCloner()
        : this(OperatingSystem.IsMacOS, NativeCloneFile)
    {
    }

    internal ApfsDirectoryCloner(Func<bool> isMacOS, CloneFileCall cloneFile)
    {
        this.isMacOS = isMacOS;
        this.cloneFile = cloneFile;
    }

    public DirectoryCloneResult Clone(string source, string target)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(source);
        ArgumentException.ThrowIfNullOrWhiteSpace(target);
        if (!isMacOS())
        {
            return new(false, null, "clonefile(2) requires macOS");
        }

        Marshal.SetLastSystemError(0);
        if (cloneFile(NullTerminated(source), NullTerminated(target), 0) == 0)
        {
            return new(true, null, null);
        }

        var errno = Marshal.GetLastPInvokeError();
        return new(
            false,
            errno,
            $"clonefile(2) failed: errno={errno} ({Marshal.GetPInvokeErrorMessage(errno)})");
    }

    private static byte[] NullTerminated(string path)
    {
        var encoded = Encoding.UTF8.GetBytes(path);
        var buffer = new byte[encoded.Length + 1];
        encoded.CopyTo(buffer, 0);
        return buffer;
    }
}
