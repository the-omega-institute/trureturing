using System.Runtime.InteropServices;

namespace StrataLint.ArchitectureTests;

internal static class PosixFileType
{
    private const int NativeStatBufferSize = 256;
    private const int FileTypeMask = 0xF000;
    private const int RegularFileType = 0x8000;

    internal static bool IsRegularFile(string path)
    {
        if (path.Contains('\0', StringComparison.Ordinal)) return false;

        var encodedPath = Marshal.StringToCoTaskMemUTF8(path);
        var statBuffer = Marshal.AllocHGlobal(NativeStatBufferSize);
        try
        {
            int mode;
            if (OperatingSystem.IsLinux())
            {
                mode = ReadLinuxMode(encodedPath, statBuffer);
            }
            else if (OperatingSystem.IsMacOS()
                     && RuntimeInformation.ProcessArchitecture is Architecture.Arm64 or Architecture.X64)
            {
                mode = ReadDarwinMode(encodedPath, statBuffer);
            }
            else
            {
                return false;
            }
            return mode >= 0 && (mode & FileTypeMask) == RegularFileType;
        }
        catch (Exception exception) when (exception is DllNotFoundException
                                          or EntryPointNotFoundException
                                          or BadImageFormatException)
        {
            return false;
        }
        finally
        {
            Marshal.FreeHGlobal(statBuffer);
            Marshal.FreeCoTaskMem(encodedPath);
        }
    }

    private static int ReadLinuxMode(nint path, nint statBuffer)
    {
        const int atFileDescriptorCurrentWorkingDirectory = -100;
        const int atSymlinkNoFollow = 0x100;
        const uint statxType = 0x0001;
        const int statxModeOffset = 28;

        // struct statx is a fixed Linux UAPI layout on every supported architecture.
        if (StatxLinux(
                atFileDescriptorCurrentWorkingDirectory,
                path,
                atSymlinkNoFollow,
                statxType,
                statBuffer) != 0
            || (unchecked((uint)Marshal.ReadInt32(statBuffer)) & statxType) == 0)
        {
            return -1;
        }
        return unchecked((ushort)Marshal.ReadInt16(statBuffer, statxModeOffset));
    }

    private static int ReadDarwinMode(nint path, nint statBuffer)
    {
        const int statModeOffset = 4;

        // Darwin's 64-bit struct stat ABI places st_mode at byte offset four.
        return LStatDarwin(path, statBuffer) == 0
            ? unchecked((ushort)Marshal.ReadInt16(statBuffer, statModeOffset))
            : -1;
    }

    [DllImport("libc.so.6", EntryPoint = "statx", SetLastError = true)]
    private static extern int StatxLinux(
        int directoryFileDescriptor,
        nint path,
        int flags,
        uint mask,
        nint statBuffer);

    [DllImport("libSystem.B.dylib", EntryPoint = "lstat", SetLastError = true)]
    private static extern int LStatDarwin(nint path, nint statBuffer);
}
