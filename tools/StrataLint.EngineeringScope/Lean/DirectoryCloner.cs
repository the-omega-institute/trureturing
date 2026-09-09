using System.Runtime.InteropServices;
using System.Text;

namespace StrataLint.Cli;

/// <summary>
/// Result of one directory-clone boundary call. Attempts counts native clonefile calls.
/// </summary>
internal sealed record DirectoryCloneResult(
    bool Succeeded,
    bool Retryable,
    int? Errno,
    int Attempts,
    string? Message);

internal sealed record ClonefileReceipt(
    int Attempts,
    IReadOnlyList<int> Errnos,
    string? CleanupError)
{
    internal static ClonefileReceipt NotRun { get; } = new(0, [], null);

    internal int? LastErrno => Errnos.Count == 0 ? null : Errnos[^1];
}

internal interface IDirectoryCloner
{
    DirectoryCloneResult Clone(string source, string target);
}

/// <summary>
/// Clones a directory tree with a single APFS clonefile(2) call. The kernel walks the
/// hierarchy itself, so the measured 14 GiB/133,406-file cache takes about four seconds,
/// shares physical blocks, and avoids a system call per entry.
/// </summary>
internal sealed class ApfsDirectoryCloner : IDirectoryCloner
{
    private enum DarwinErrno
    {
        OperationNotPermitted = 1,
        NoSuchFileOrDirectory = 2,
        ResourceDeadlockAvoided = 11,
        PermissionDenied = 13,
        FileExists = 17,
        CrossDeviceLink = 18,
        NotDirectory = 20,
        InvalidArgument = 22,
        NoSpaceLeft = 28,
        ReadOnlyFileSystem = 30,
        OperationNotSupported = 45,
        TooManySymbolicLinks = 62,
        FileNameTooLong = 63,
        CapabilitiesInsufficient = 107,
    }

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
            return new(false, false, null, 0, "clonefile(2) requires macOS");
        }

        Marshal.SetLastSystemError(0);
        if (cloneFile(NullTerminated(source), NullTerminated(target), 0) == 0)
        {
            return new(true, false, null, 1, null);
        }

        var errno = Marshal.GetLastPInvokeError();
        return new(
            false,
            IsRetryable(errno),
            errno,
            1,
            $"clonefile(2) failed: errno={errno} ({Marshal.GetPInvokeErrorMessage(errno)})");
    }

    internal static bool IsRetryable(int errno) => (DarwinErrno)errno switch
    {
        // Exhaustive projection of clonefile(2) ERRORS whose stated condition is a
        // fixed input/path/capability/capacity precondition. Values come from Darwin
        // sys/errno.h. EIO and generic interruption/unavailable/busy failures can change.
        DarwinErrno.OperationNotPermitted
            or DarwinErrno.NoSuchFileOrDirectory
            or DarwinErrno.ResourceDeadlockAvoided
            or DarwinErrno.PermissionDenied
            or DarwinErrno.FileExists
            or DarwinErrno.CrossDeviceLink
            or DarwinErrno.NotDirectory
            or DarwinErrno.InvalidArgument
            or DarwinErrno.NoSpaceLeft
            or DarwinErrno.ReadOnlyFileSystem
            or DarwinErrno.OperationNotSupported
            or DarwinErrno.TooManySymbolicLinks
            or DarwinErrno.FileNameTooLong
            or DarwinErrno.CapabilitiesInsufficient => false,

        // The observed incident has no captured errno yet. Unknown values get the same
        // bounded 3.75 s budget so a future receipt can support tighter classification.
        _ => true,
    };

    private static byte[] NullTerminated(string path)
    {
        var encoded = Encoding.UTF8.GetBytes(path);
        var buffer = new byte[encoded.Length + 1];
        encoded.CopyTo(buffer, 0);
        return buffer;
    }
}
