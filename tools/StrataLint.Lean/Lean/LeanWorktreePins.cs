using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Runtime.InteropServices;
using Microsoft.Win32.SafeHandles;
using StrataLint.Engine;

namespace StrataLint.EngineeringScope;

internal sealed record LeanPinSet(byte[] LeanToolchain, byte[] LakeManifest, string MathlibRevision)
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);
    internal string Sha256 => "sha256:" + Convert.ToHexStringLower(
        SHA256.HashData(Encoding.ASCII.GetBytes(MathlibRevision)));

    internal static LeanPinSet ReadBase(
        string repositoryRoot,
        string revision,
        IWorktreeProcessRunner runner)
    {
        var toolchain = ReadRevisionFile(repositoryRoot, revision, "lean-toolchain", runner);
        var manifest = ReadRevisionFile(repositoryRoot, revision, "lake-manifest.json", runner);
        return Create(toolchain, manifest);
    }

    internal static LeanPinSet? TryReadWorktree(string root, out string? reason)
    {
        var toolchainPath = Path.Combine(root, "lean-toolchain");
        var manifestPath = Path.Combine(root, "lake-manifest.json");
        if (!File.Exists(toolchainPath) || !File.Exists(manifestPath))
        {
            reason = "pin files are absent";
            return null;
        }

        try
        {
            reason = null;
            return Create(File.ReadAllBytes(toolchainPath), File.ReadAllBytes(manifestPath));
        }
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException
            or JsonException or InvalidOperationException or KeyNotFoundException)
        {
            reason = $"pin files are unreadable: {exception.Message}";
            return null;
        }
    }

    // Exact bytes guard an in-flight warming operation; they never select a seed.
    internal bool HasSameBytes(LeanPinSet other) =>
        LeanToolchain.AsSpan().SequenceEqual(other.LeanToolchain)
        && LakeManifest.AsSpan().SequenceEqual(other.LakeManifest);

    internal bool SamePartition(LeanPinSet other) => MathlibRevision == other.MathlibRevision;

    internal static LeanPinSet Create(byte[] toolchain, byte[] manifest)
    {
        using var document = JsonDocument.Parse(manifest);
        var packages = document.RootElement.GetProperty("packages");
        var mathlib = packages.EnumerateArray().Where(static package =>
            package.TryGetProperty("name", out var name) && name.GetString() == "mathlib").ToArray();
        if (mathlib.Length != 1
            || !mathlib[0].TryGetProperty("rev", out var revision)
            || revision.ValueKind != JsonValueKind.String
            || !ValidRevision(revision.GetString()))
            throw new InvalidOperationException("manifest requires exactly one mathlib package with a resolved 40-hex revision");
        return new LeanPinSet(toolchain, manifest, revision.GetString()!);
    }

    internal static bool ValidRevision(string? revision) => revision is { Length: 40 }
        && revision.All(static character => character is >= '0' and <= '9' or >= 'a' and <= 'f');

    private static byte[] ReadRevisionFile(
        string repositoryRoot,
        string revision,
        string path,
        IWorktreeProcessRunner runner)
    {
        var result = runner.Run(
            "git",
            ["show", $"{revision}:{path}"],
            repositoryRoot,
            BoundedProcessRunner.HangDetectionBudget);
        if (result.ExitCode == 0) return result.StandardOutput;

        var error = StrictUtf8.GetString(result.StandardError).Trim();
        throw new InvalidOperationException(
            error.Length == 0
                ? $"base revision does not contain {path}"
                : $"could not read {path} from base: {error}");
    }
}

internal enum LeanCacheStampState
{
    Match,
    Missing,
    Corrupt,
    Mismatch,
}

internal sealed record LeanCacheStampInspection(LeanCacheStampState State, string? Reason);

internal static class LeanCacheStamp
{
    // The stamp records pin identity only. Cache completeness is live state and is checked on
    // every ensure/writer admission instead of being inferred from this durable identity record.
    private const string Schema = "stratalint-lean-cache-v2";
    private const string FileName = ".stratalint-lean-cache-stamp.json";
    private static string Os => OperatingSystem.IsMacOS() ? "darwin"
        : OperatingSystem.IsWindows() ? "windows" : "linux";
    private static string Arch => RuntimeInformation.ProcessArchitecture.ToString().ToLowerInvariant();

    internal static string PathFor(string lake) => Path.Combine(lake, FileName);

    internal static void Write(string lake, LeanPinSet pins)
    {
        Write(lake, pins, overwrite: true);
    }

    internal static void WriteNew(string lake, LeanPinSet pins)
    {
        Write(lake, pins, overwrite: false);
    }

    private static void Write(string lake, LeanPinSet pins, bool overwrite)
    {
        Directory.CreateDirectory(lake);
        var path = PathFor(lake);
        var temporary = Path.Combine(lake, $".stratalint-lean-cache-stamp.{Path.GetRandomFileName()}.tmp");
        try
        {
            File.WriteAllText(
                temporary,
                JsonSerializer.Serialize(new
                {
                    schema = Schema,
                    mathlib_revision = pins.MathlibRevision,
                    os = Os,
                    arch = Arch,
                }) + "\n",
                new UTF8Encoding(false));
            File.Move(temporary, path, overwrite);
        }
        finally
        {
            if (File.Exists(temporary)) File.Delete(temporary);
        }
    }

    internal static LeanCacheStampInspection Inspect(string lake, LeanPinSet pins)
    {
        var path = PathFor(lake);
        if (!File.Exists(path))
        {
            return Directory.Exists(path)
                ? new LeanCacheStampInspection(
                    LeanCacheStampState.Corrupt,
                    "cache producer stamp is not a regular file")
                : new LeanCacheStampInspection(
                    LeanCacheStampState.Missing,
                    "cache producer stamp is absent");
        }

        try
        {
            using var document = JsonDocument.Parse(File.ReadAllBytes(path));
            var root = document.RootElement;
            if (root.ValueKind != JsonValueKind.Object
                || !root.TryGetProperty("schema", out var schema)
                || schema.ValueKind != JsonValueKind.String
                || schema.GetString() != Schema
                || !root.TryGetProperty("mathlib_revision", out var revision)
                || revision.ValueKind != JsonValueKind.String
                || !LeanPinSet.ValidRevision(revision.GetString())
                || !root.TryGetProperty("os", out var os)
                || os.ValueKind != JsonValueKind.String
                || !root.TryGetProperty("arch", out var arch)
                || arch.ValueKind != JsonValueKind.String)
            {
                return new LeanCacheStampInspection(
                    LeanCacheStampState.Corrupt,
                    "cache producer stamp has an unknown or invalid schema");
            }

            if (revision.GetString() != pins.MathlibRevision
                || os.GetString() != Os || arch.GetString() != Arch)
            {
                return new LeanCacheStampInspection(
                    LeanCacheStampState.Mismatch,
                    "cache producer stamp mathlib partition or platform does not match");
            }

            return new LeanCacheStampInspection(LeanCacheStampState.Match, null);
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException
            or JsonException
            or FormatException)
        {
            return new LeanCacheStampInspection(
                LeanCacheStampState.Corrupt,
                $"cache producer stamp is unreadable: {exception.Message}");
        }
    }

    internal static bool Matches(string lake, LeanPinSet pins, out string? reason)
    {
        var inspection = Inspect(lake, pins);
        reason = inspection.Reason;
        return inspection.State == LeanCacheStampState.Match;
    }
}

internal sealed class LeanCacheGuard : IDisposable
{
    private const int LockExclusive = 2;
    private const int LockNonBlocking = 4;
    private const uint LockFileFailImmediately = 1;
    private const uint LockFileExclusiveLock = 2;
    private readonly FileStream stream;
    private bool locked = true;

    private LeanCacheGuard(FileStream stream) => this.stream = stream;

    internal int Descriptor => stream.SafeFileHandle.DangerousGetHandle().ToInt32();

    internal bool HasWriterSession()
    {
        if (OperatingSystem.IsWindows()) return false;
        stream.Position = 0;
        using var reader = new StreamReader(stream, leaveOpen: true);
        var line = reader.ReadLine();
        if (line is null) return false;
        var fields = line.Split(' ');
        if (fields.Length != 2 || !int.TryParse(fields[0], System.Globalization.NumberStyles.None,
            System.Globalization.CultureInfo.InvariantCulture, out var group) || group <= 1)
            throw new InvalidOperationException("invalid cache writer instance identity in " + stream.Name
                + "; stop cache users before removing an obsolete reservation");
        if (!LeanCacheWriterIdentity.IsCurrentBoot(fields[1])) return false;
        // A numeric session can be reused. Its living members must also carry this
        // dispatch's boot/process identity, inherited through the supported Lake exec tree.
        // Foreground tools such as timeout can start another group in the same session.
        // A departed leader does not release the reservation while that writer remains.
        var processes = System.Diagnostics.Process.GetProcesses();
        try
        {
            foreach (var process in processes)
            {
                var session = GetSession(process.Id);
                if (session == group && LeanCacheWriterIdentity.IsMember(process.Id, fields[1])) return true;
                if (session < 0 && Marshal.GetLastPInvokeError() != 3)
                    throw new InvalidOperationException("cannot inspect cache writer session membership");
            }
            return false;
        }
        finally { foreach (var process in processes) process.Dispose(); }
    }

    internal void SetInheritable(bool inherit)
    {
        if (Fcntl(Descriptor, 2, inherit ? 0 : 1) < 0) // F_SETFD, FD_CLOEXEC
            throw new IOException("cannot transfer cache writer guard to child");
    }

    internal void ClearExitedSession() => stream.SetLength(0);

    internal static LeanCacheGuard? TryAcquireExclusive(string lake, string directory) => TryAcquire(lake, directory);

    internal static string PhysicalPath(string path)
    {
        var full = Path.GetFullPath(path);
        if (OperatingSystem.IsWindows()) return full;
        var resolved = ResolveExisting(full);
        if (resolved is not null) return resolved;
        var parent = Path.GetDirectoryName(full);
        var resolvedParent = parent is null ? null : ResolveExisting(parent);
        return resolvedParent is null ? full : Path.Combine(resolvedParent, Path.GetFileName(full));
    }

    public void Dispose()
    {
        if (locked)
        {
            if (OperatingSystem.IsWindows())
            {
                _ = UnlockFile(stream.SafeFileHandle, 0, 0, 1, 0);
            }
            // POSIX flock follows the open file description. Closing our descriptor keeps
            // the startup guard held by an inherited launcher; LOCK_UN would release both.
            locked = false;
        }
        stream.Dispose();
    }

    private static LeanCacheGuard? TryAcquire(string lake, string directory)
    {
        Directory.CreateDirectory(directory);
        var address = Convert.ToHexStringLower(SHA256.HashData(
            Encoding.UTF8.GetBytes(PhysicalPath(lake))));
        FileStream stream;
        try
        {
            stream = new FileStream(
                Path.Combine(directory, address + ".lock"),
                FileMode.OpenOrCreate,
                FileAccess.ReadWrite,
                FileShare.ReadWrite | FileShare.Delete,
                bufferSize: 1);
        }
        catch (IOException)
        {
            return null;
        }
        var acquired = OperatingSystem.IsWindows()
            ? TryLockWindows(stream.SafeFileHandle)
            : Flock(
                stream.SafeFileHandle,
                LockExclusive | LockNonBlocking) == 0;
        if (acquired)
        {
            var guard = new LeanCacheGuard(stream);
            try
            {
                if (!guard.HasWriterSession()) return guard;
            }
            catch { guard.Dispose(); throw; }
        }
        stream.Dispose();
        return null;
    }

    private static bool TryLockWindows(SafeFileHandle handle)
    {
        var overlapped = Marshal.AllocHGlobal(Marshal.SizeOf<NativeOverlapped>());
        try
        {
            Marshal.StructureToPtr(default(NativeOverlapped), overlapped, false);
            var flags = LockFileFailImmediately | LockFileExclusiveLock;
            return LockFileEx(handle, flags, 0, 1, 0, overlapped);
        }
        finally
        {
            Marshal.FreeHGlobal(overlapped);
        }
    }

    private static string? ResolveExisting(string path)
    {
        var pointer = RealPath(path, IntPtr.Zero);
        if (pointer == IntPtr.Zero) return null;
        try
        {
            return Marshal.PtrToStringUTF8(pointer);
        }
        finally
        {
            Free(pointer);
        }
    }

    [DllImport("libc", EntryPoint = "flock", SetLastError = true)]
    private static extern int Flock(SafeFileHandle handle, int operation);

    [DllImport("libc", EntryPoint = "fcntl", SetLastError = true)]
    private static extern int Fcntl(int descriptor, int command, int flags);

    [DllImport("libc", EntryPoint = "getsid", SetLastError = true)]
    private static extern int GetSession(int process);

    [DllImport("libc", EntryPoint = "realpath", SetLastError = true)]
    private static extern IntPtr RealPath([MarshalAs(UnmanagedType.LPUTF8Str)] string path, IntPtr buffer);

    [DllImport("libc", EntryPoint = "free")]
    private static extern void Free(IntPtr pointer);

    [DllImport("kernel32.dll", SetLastError = true)]
    [return: MarshalAs(UnmanagedType.Bool)]
    private static extern bool LockFileEx(
        SafeFileHandle file,
        uint flags,
        uint reserved,
        uint bytesLow,
        uint bytesHigh,
        IntPtr overlapped);

    [DllImport("kernel32.dll", SetLastError = true)]
    [return: MarshalAs(UnmanagedType.Bool)]
    private static extern bool UnlockFile(
        SafeFileHandle file,
        uint offsetLow,
        uint offsetHigh,
        uint bytesLow,
        uint bytesHigh);

    [StructLayout(LayoutKind.Sequential)]
    private struct NativeOverlapped
    {
        internal IntPtr Internal;
        internal IntPtr InternalHigh;
        internal uint Offset;
        internal uint OffsetHigh;
        internal IntPtr EventHandle;
    }
}

internal sealed class LeanCacheWriterGuard : IDisposable
{
    private readonly string lake;
    private LeanCacheGuard? guard;

    private LeanCacheWriterGuard(string lake, LeanCacheGuard guard)
    {
        this.lake = LeanCacheGuard.PhysicalPath(lake);
        this.guard = guard;
    }

    internal LeanCacheGuard ProcessGuard => guard ?? throw new ObjectDisposedException(nameof(LeanCacheWriterGuard));

    internal static LeanCacheWriterGuard? TryAcquire(string lake, string directory)
    {
        var guard = LeanCacheGuard.TryAcquireExclusive(lake, directory);
        return guard is null ? null : new LeanCacheWriterGuard(lake, guard);
    }

    internal void RequireOwnershipOf(string expectedLake)
    {
        ObjectDisposedException.ThrowIf(guard is null, this);
        var expected = LeanCacheGuard.PhysicalPath(expectedLake);
        if (!string.Equals(lake, expected, StringComparison.Ordinal))
        {
            throw new InvalidOperationException(
                $"cache writer guard owns {lake}, not the requested target {expected}");
        }
    }

    public void Dispose()
    {
        guard?.Dispose();
        guard = null;
    }
}

internal static class GitWorktreeInventory
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static void FetchRemoteBase(
        string repositoryRoot,
        string baseRevision,
        IWorktreeProcessRunner runner)
    {
        var slash = baseRevision.IndexOf('/', StringComparison.Ordinal);
        if (slash <= 0) return;
        var candidateRemote = baseRevision[..slash];
        var remotes = RunGit(
            repositoryRoot,
            ["remote"],
            runner,
            "could not enumerate git remotes");
        var remoteNames = StrictUtf8.GetString(remotes.StandardOutput)
            .Split('\n', StringSplitOptions.RemoveEmptyEntries | StringSplitOptions.TrimEntries);
        if (!remoteNames.Contains(candidateRemote, StringComparer.Ordinal)) return;

        RunGit(
            repositoryRoot,
            ["fetch", "--prune", candidateRemote],
            runner,
            $"git fetch {candidateRemote} failed");
    }

    private static ProcessOutput RunGit(
        string repositoryRoot,
        IReadOnlyList<string> arguments,
        IWorktreeProcessRunner runner,
        string fallback)
    {
        var result = runner.Run("git", arguments, repositoryRoot, TimeSpan.FromSeconds(120));
        if (result.ExitCode == 0) return result;
        var error = StrictUtf8.GetString(result.StandardError).Trim();
        throw new InvalidOperationException(error.Length == 0 ? fallback : error);
    }
}
