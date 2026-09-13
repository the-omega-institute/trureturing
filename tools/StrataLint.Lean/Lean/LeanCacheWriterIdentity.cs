using System.Diagnostics;
using System.Globalization;
using System.Runtime.InteropServices;
using System.Text;

namespace StrataLint.EngineeringScope;

internal static class LeanCacheWriterIdentity
{
    internal const string EnvironmentName = "STRATALINT_LAKE_WRITER_INSTANCE";
    private static readonly Lazy<string> Boot = new(ReadBoot);
    private static long dispatch;

    internal static string Create()
    {
        using var owner = Process.GetCurrentProcess();
        // StartTime comes from the kernel, not a deadline. The ordinal distinguishes
        // sequential commands of the same process; exec preserves the inherited marker.
        return string.Create(CultureInfo.InvariantCulture,
            $"{Boot.Value}:{owner.Id}:{owner.StartTime.ToUniversalTime().Ticks}:{Interlocked.Increment(ref dispatch)}");
    }

    internal static bool IsCurrentBoot(string identity)
    {
        var fields = identity.Split(':');
        if (fields.Length != 4 || !Guid.TryParseExact(fields[0], "D", out _)
            || !int.TryParse(fields[1], NumberStyles.None, CultureInfo.InvariantCulture, out var process) || process <= 1
            || !long.TryParse(fields[2], NumberStyles.None, CultureInfo.InvariantCulture, out var birth) || birth <= 0
            || !long.TryParse(fields[3], NumberStyles.None, CultureInfo.InvariantCulture, out var sequence) || sequence <= 0)
            throw new InvalidOperationException("invalid cache writer instance identity");
        return fields[0].Equals(Boot.Value, StringComparison.OrdinalIgnoreCase);
    }

    internal static bool IsMember(int process, string identity)
    {
        byte[] bytes;
        if (OperatingSystem.IsLinux())
        {
            try { bytes = File.ReadAllBytes($"/proc/{process}/environ"); }
            catch (IOException) when (!Directory.Exists($"/proc/{process}")) { return false; }
        }
        else if (OperatingSystem.IsMacOS())
        {
            // KERN_PROCARGS2 is the kernel's exec argument/environment image. Skip argv
            // explicitly: an argument resembling the marker is not inherited identity.
            var capacity = ReadSysctl("kern.argmax");
            bytes = new byte[BitConverter.ToInt32(capacity)];
            nuint size = (nuint)bytes.Length;
            if (Sysctl([1, 49, process], 3, bytes, ref size, IntPtr.Zero, 0) != 0)
            {
                var error = Marshal.GetLastPInvokeError();
                if (error == 3 || ProcessExited(process)) return false;
                throw new IOException("cannot inspect cache writer environment: errno " + error);
            }
            var length = checked((int)size);
            if (length == 0) return false;
            if (length < sizeof(int)) throw new IOException("invalid kernel process arguments");
            var count = BitConverter.ToInt32(bytes);
            var index = sizeof(int);
            SkipString(bytes, ref index, length); // executable path
            while (index < length && bytes[index] == 0) index++;
            for (var i = 0; i < count; i++) SkipString(bytes, ref index, length);
            bytes = bytes[index..length];
        }
        else throw new PlatformNotSupportedException("Cache writer instance inspection requires macOS or Linux.");
        var marker = EnvironmentName + "=" + identity;
        foreach (var entry in Encoding.UTF8.GetString(bytes).Split('\0'))
        {
            if (entry.Length == 0) break;
            if (entry == marker) return true;
        }
        return false;
    }

    private static bool ProcessExited(int process)
    {
        try
        {
            using var candidate = Process.GetProcessById(process);
            return candidate.HasExited;
        }
        catch (ArgumentException) { return true; }
    }

    private static void SkipString(byte[] bytes, ref int index, int length)
    {
        while (index < length && bytes[index] != 0) index++;
        if (index >= length) throw new IOException("unterminated kernel process argument");
        index++;
    }

    private static string ReadBoot()
    {
        var value = OperatingSystem.IsMacOS()
            ? Encoding.UTF8.GetString(ReadSysctl("kern.bootsessionuuid")).TrimEnd('\0')
            : File.ReadAllText("/proc/sys/kernel/random/boot_id").Trim();
        if (!Guid.TryParseExact(value, "D", out _)) throw new IOException("invalid kernel boot identity");
        return value;
    }

    private static byte[] ReadSysctl(string name)
    {
        nuint size = 0;
        if (SysctlByName(name, null, ref size, IntPtr.Zero, 0) != 0)
            throw new IOException("cannot read kernel " + name);
        var bytes = new byte[checked((int)size)];
        if (SysctlByName(name, bytes, ref size, IntPtr.Zero, 0) != 0)
            throw new IOException("cannot read kernel " + name);
        return bytes;
    }

    [DllImport("libc", EntryPoint = "sysctl", SetLastError = true)]
    private static extern int Sysctl(int[] name, uint count, byte[] value, ref nuint size, IntPtr input, nuint inputSize);

    [DllImport("libc", EntryPoint = "sysctlbyname", SetLastError = true)]
    private static extern int SysctlByName(string name, byte[]? value, ref nuint size, IntPtr input, nuint inputSize);
}
