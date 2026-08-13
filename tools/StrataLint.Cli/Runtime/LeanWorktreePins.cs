using System.Buffers.Binary;
using System.Security.Cryptography;
using System.Text;
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

    private static LeanPinSet Create(byte[] toolchain, byte[] manifest)
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
            TimeSpan.FromSeconds(30));
        if (result.ExitCode == 0) return result.StandardOutput;

        var error = StrictUtf8.GetString(result.StandardError).Trim();
        throw new InvalidOperationException(
            error.Length == 0
                ? $"base revision does not contain {path}"
                : $"could not read {path} from base: {error}");
    }
}

internal sealed record LeanCacheDonorSelection(string? Donor, string? Notice);

internal static class GitWorktreeInventory
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static LeanCacheDonorSelection SelectDonor(
        string repositoryRoot,
        LeanPinSet basePins,
        IWorktreeProcessRunner runner)
    {
        var roots = ReadRoots(repositoryRoot, runner);
        var ordered = new[] { Path.GetFullPath(repositoryRoot) }
            .Concat(roots)
            .Distinct(StringComparer.Ordinal);
        var sawCache = false;
        var sawMismatch = false;
        var sawSymlink = false;
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

            if (basePins.HasSameBytes(pins))
            {
                return new LeanCacheDonorSelection(Path.GetFullPath(root), null);
            }

            sawMismatch = true;
        }

        var notice = sawMismatch
            ? "existing .lake donor pin bytes do not match the requested base"
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
