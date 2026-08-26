using System.Buffers.Binary;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Runtime.InteropServices;
using Microsoft.Win32.SafeHandles;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record LeanPinSet(byte[] LeanToolchain, byte[] LakeManifest, string Sha256)
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

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
        catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
        {
            reason = $"pin files are unreadable: {exception.Message}";
            return null;
        }
    }

    internal bool HasSameBytes(LeanPinSet other) =>
        LeanToolchain.AsSpan().SequenceEqual(other.LeanToolchain)
        && LakeManifest.AsSpan().SequenceEqual(other.LakeManifest);

    internal static LeanPinSet Create(byte[] toolchain, byte[] manifest)
    {
        using var hash = IncrementalHash.CreateHash(HashAlgorithmName.SHA256);
        AppendField(hash, "lean-toolchain", toolchain);
        AppendField(hash, "lake-manifest.json", manifest);
        return new LeanPinSet(
            toolchain,
            manifest,
            "sha256:" + Convert.ToHexStringLower(hash.GetHashAndReset()));
    }

    private static void AppendField(IncrementalHash hash, string name, byte[] value)
    {
        var nameBytes = Encoding.ASCII.GetBytes(name);
        Span<byte> length = stackalloc byte[4];
        BinaryPrimitives.WriteInt32BigEndian(length, nameBytes.Length);
        hash.AppendData(length);
        hash.AppendData(nameBytes);
        BinaryPrimitives.WriteInt32BigEndian(length, value.Length);
        hash.AppendData(length);
        hash.AppendData(value);
    }

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
    private const string Schema = "stratalint-lean-cache-v1";
    private const string FileName = ".stratalint-lean-cache-stamp.json";

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
                    pin_sha256 = pins.Sha256,
                    lean_toolchain_base64 = Convert.ToBase64String(pins.LeanToolchain),
                    lake_manifest_base64 = Convert.ToBase64String(pins.LakeManifest),
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
                || !root.TryGetProperty("pin_sha256", out var sha256)
                || sha256.ValueKind != JsonValueKind.String
                || !root.TryGetProperty("lean_toolchain_base64", out var toolchain)
                || toolchain.ValueKind != JsonValueKind.String
                || !root.TryGetProperty("lake_manifest_base64", out var manifest)
                || manifest.ValueKind != JsonValueKind.String)
            {
                return new LeanCacheStampInspection(
                    LeanCacheStampState.Corrupt,
                    "cache producer stamp has an unknown or invalid schema");
            }

            var toolchainBytes = Convert.FromBase64String(toolchain.GetString()!);
            var manifestBytes = Convert.FromBase64String(manifest.GetString()!);
            var embeddedPins = LeanPinSet.Create(toolchainBytes, manifestBytes);
            if (sha256.GetString() != embeddedPins.Sha256)
            {
                return new LeanCacheStampInspection(
                    LeanCacheStampState.Corrupt,
                    "cache producer stamp pin hash is inconsistent with its embedded pin bytes");
            }

            if (sha256.GetString() != pins.Sha256 || !embeddedPins.HasSameBytes(pins))
            {
                return new LeanCacheStampInspection(
                    LeanCacheStampState.Mismatch,
                    "cache producer stamp pin bytes do not match the requested pins");
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
    private const int LockShared = 1;
    private const int LockExclusive = 2;
    private const int LockNonBlocking = 4;
    private const int LockUnlock = 8;
    private const uint LockFileFailImmediately = 1;
    private const uint LockFileExclusiveLock = 2;
    private readonly FileStream stream;
    private bool locked = true;

    private LeanCacheGuard(FileStream stream) => this.stream = stream;

    internal static LeanCacheGuard? TryAcquireShared(string lake) => TryAcquire(lake, shared: true);

    internal static LeanCacheGuard? TryAcquireExclusive(string lake) => TryAcquire(lake, shared: false);

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
            else
            {
                _ = Flock(stream.SafeFileHandle, LockUnlock);
            }
            locked = false;
        }
        stream.Dispose();
    }

    private static LeanCacheGuard? TryAcquire(string lake, bool shared)
    {
        var directory = Path.Combine(Path.GetTempPath(), "stratalint-lean-cache-guards");
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
                FileShare.ReadWrite | FileShare.Delete);
        }
        catch (IOException)
        {
            return null;
        }
        var acquired = OperatingSystem.IsWindows()
            ? TryLockWindows(stream.SafeFileHandle, shared)
            : Flock(
                stream.SafeFileHandle,
                (shared ? LockShared : LockExclusive) | LockNonBlocking) == 0;
        if (acquired) return new LeanCacheGuard(stream);
        stream.Dispose();
        return null;
    }

    private static bool TryLockWindows(SafeFileHandle handle, bool shared)
    {
        var overlapped = Marshal.AllocHGlobal(Marshal.SizeOf<NativeOverlapped>());
        try
        {
            Marshal.StructureToPtr(default(NativeOverlapped), overlapped, false);
            var flags = LockFileFailImmediately | (shared ? 0u : LockFileExclusiveLock);
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

    internal static LeanCacheWriterGuard? TryAcquire(string lake)
    {
        var guard = LeanCacheGuard.TryAcquireExclusive(lake);
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

internal static class LeanCacheBusyProbe
{
    internal static bool IsBusy(string root, IWorktreeProcessRunner runner)
    {
        ProcessOutput output;
        try
        {
            output = runner.Run(
                "lsof",
                ["-Fpcn", "-a", "-d", "cwd"],
                Path.GetTempPath(),
                BoundedProcessRunner.HangDetectionBudget);
        }
        catch (Exception exception) when (exception is IOException
            or UnauthorizedAccessException
            or InvalidOperationException
            or TimeoutException)
        {
            return false;
        }
        if (output.ExitCode != 0) return false;

        var target = LeanCacheGuard.PhysicalPath(root).TrimEnd(Path.DirectorySeparatorChar)
            + Path.DirectorySeparatorChar;
        string? command = null;
        foreach (var line in Encoding.UTF8.GetString(output.StandardOutput).Split('\n'))
        {
            if (line.StartsWith('c'))
            {
                command = line[1..];
                continue;
            }
            if (!line.StartsWith('n') || !IsLeanWriter(command)) continue;
            var cwd = LeanCacheGuard.PhysicalPath(line[1..]).TrimEnd(Path.DirectorySeparatorChar)
                + Path.DirectorySeparatorChar;
            if (cwd.StartsWith(target, StringComparison.Ordinal)) return true;
        }
        return false;
    }

    private static bool IsLeanWriter(string? command) => command is not null
        && (command.Contains("lake", StringComparison.OrdinalIgnoreCase)
            || command.Contains("lean", StringComparison.OrdinalIgnoreCase));
}

internal sealed class LeanCacheDonorSelection : IDisposable
{
    private LeanCacheGuard? guard;

    internal LeanCacheDonorSelection(
        string? donor,
        string? notice,
        LeanCacheGuard? guard = null,
        OleanWarmthInspection? projectWarmth = null)
    {
        Donor = donor;
        Notice = notice;
        this.guard = guard;
        ProjectWarmth = projectWarmth;
    }

    internal string? Donor { get; }

    internal string? Notice { get; }

    internal OleanWarmthInspection? ProjectWarmth { get; }

    internal LeanCacheGuard? TakeGuard()
    {
        var owned = guard;
        guard = null;
        return owned;
    }

    public void Dispose() => guard?.Dispose();
}

internal static class GitWorktreeInventory
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static LeanCacheDonorSelection SelectDonor(
        string repositoryRoot,
        LeanPinSet basePins,
        IWorktreeProcessRunner runner) =>
        SelectDonor(
            repositoryRoot,
            basePins,
            runner,
            FileSystemLeanCacheStateProbe.Instance,
            requireProjectWarm: false);

    internal static LeanCacheDonorSelection SelectDonor(
        string repositoryRoot,
        LeanPinSet basePins,
        IWorktreeProcessRunner runner,
        ILeanCacheStateProbe stateProbe,
        bool requireProjectWarm)
    {
        ArgumentNullException.ThrowIfNull(stateProbe);
        var targetRoot = LeanCacheGuard.PhysicalPath(repositoryRoot);
        var ordered = ReadRoots(repositoryRoot, runner)
            .Select(LeanCacheGuard.PhysicalPath)
            .Where(root => !string.Equals(root, targetRoot, StringComparison.Ordinal))
            .Distinct(StringComparer.Ordinal);
        var sawCache = false;
        var sawMismatch = false;
        var sawSymlink = false;
        var sawInvalidStamp = false;
        var sawBusy = false;
        var sawColdProject = false;
        var sawProjectProbeFailure = false;
        var unreadable = new List<string>();

        foreach (var root in ordered)
        {
            var cache = Path.Combine(root, ".lake");
            if (!Directory.Exists(cache)) continue;
            sawCache = true;
            try
            {
                if (File.GetAttributes(cache).HasFlag(FileAttributes.ReparsePoint))
                {
                    sawSymlink = true;
                    continue;
                }
            }
            catch (Exception exception) when (exception is IOException or UnauthorizedAccessException)
            {
                unreadable.Add($"{root}: {exception.Message}");
                continue;
            }

            var pins = LeanPinSet.TryReadWorktree(root, out var reason);
            if (pins is null)
            {
                unreadable.Add($"{root}: {reason}");
                continue;
            }

            if (!basePins.HasSameBytes(pins))
            {
                sawMismatch = true;
                continue;
            }

            if (!LeanCacheStamp.Matches(cache, basePins, out var stampReason))
            {
                sawInvalidStamp = true;
                unreadable.Add($"{root}: {stampReason}");
                continue;
            }

            var guard = LeanCacheGuard.TryAcquireShared(cache);
            if (guard is null)
            {
                sawBusy = true;
                continue;
            }

            var verifiedPins = LeanPinSet.TryReadWorktree(root, out _);
            if (verifiedPins is null
                || !basePins.HasSameBytes(verifiedPins)
                || !LeanCacheStamp.Matches(cache, basePins, out _)
                || LeanCacheBusyProbe.IsBusy(root, runner))
            {
                guard.Dispose();
                sawBusy = true;
                continue;
            }

            var project = stateProbe.ProbeOleans(
                Path.Combine(cache, "build", "lib", "lean"));
            if (requireProjectWarm)
            {
                if (!project.IsWarm)
                {
                    guard.Dispose();
                    sawColdProject |= project.State == OleanWarmth.Cold;
                    sawProjectProbeFailure |= project.State == OleanWarmth.ProbeFailed;
                    if (project.Error is not null) unreadable.Add($"{root}: {project.Error}");
                    continue;
                }
            }

            return new LeanCacheDonorSelection(Path.GetFullPath(root), null, guard, project);
        }

        var notice = sawMismatch
            ? "existing .lake donor pin bytes do not match the requested base"
            : sawInvalidStamp
                ? $"existing .lake donor producer stamp is unusable ({string.Join("; ", unreadable)})"
                : sawProjectProbeFailure
                    ? $"existing .lake donor project warmth could not be enumerated ({string.Join("; ", unreadable)})"
                : sawColdProject
                    ? "existing .lake donor has no project olean"
                : sawBusy
                    ? "existing .lake donor is busy; refusing a non-quiescent copy"
            : sawSymlink
                ? "existing .lake donor is a symlink; shared Lean caches are forbidden"
                : unreadable.Count > 0
                    ? $"existing .lake donor is unusable ({string.Join("; ", unreadable)})"
                    : sawCache
                        ? "existing .lake donor has no readable pin files"
                        : "no existing worktree contains .lake";
        return new LeanCacheDonorSelection(null, notice);
    }

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

    private static IReadOnlyList<string> ReadRoots(
        string repositoryRoot,
        IWorktreeProcessRunner runner)
    {
        var result = RunGit(
            repositoryRoot,
            ["worktree", "list", "--porcelain", "-z"],
            runner,
            "could not enumerate git worktrees");
        var fields = StrictUtf8.GetString(result.StandardOutput).Split('\0');
        return fields
            .Where(static field => field.StartsWith("worktree ", StringComparison.Ordinal))
            .Select(static field => Path.GetFullPath(field["worktree ".Length..]))
            .ToArray();
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
