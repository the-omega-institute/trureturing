using System.Runtime.InteropServices;
using System.Text;

namespace StrataLint.Cli;

/// <summary>
/// Clones a whole directory tree. Implementations return null on success and a
/// human-readable failure reason otherwise.
/// </summary>
internal interface IDirectoryCloner
{
    string? Clone(string source, string target);
}

/// <summary>
/// Clones a directory tree with a single APFS clonefile(2) call. The kernel walks the
/// hierarchy itself, so a 14 GiB .lake with 155k files costs one system call instead of
/// one per entry: measured 3.3 s against 197.5 s for a per-file clonefile walk.
/// </summary>
internal sealed class ApfsDirectoryCloner : IDirectoryCloner
{
    [DllImport("libc", EntryPoint = "clonefile", SetLastError = true)]
    private static extern int CloneFile(byte[] source, byte[] target, uint flags);

    public string? Clone(string source, string target)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(source);
        ArgumentException.ThrowIfNullOrWhiteSpace(target);
        if (!OperatingSystem.IsMacOS())
        {
            return "clonefile(2) requires macOS";
        }

        Marshal.SetLastSystemError(0);
        if (CloneFile(NullTerminated(source), NullTerminated(target), 0) == 0)
        {
            return null;
        }

        return $"clonefile(2) failed: {Marshal.GetLastPInvokeErrorMessage()}";
    }

    private static byte[] NullTerminated(string path)
    {
        var encoded = Encoding.UTF8.GetBytes(path);
        var buffer = new byte[encoded.Length + 1];
        encoded.CopyTo(buffer, 0);
        return buffer;
    }
}
