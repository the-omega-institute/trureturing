using System.Collections.Immutable;
using System.Diagnostics;
using System.Globalization;
using System.Text;

namespace StrataLint.Cli;

// Ceremony scratch checkouts (C0 renewal, conservative replay) are multi-gigabyte git
// clones. Their owning process deletes them on the normal path, but a SIGKILL / timeout /
// crash skips that cleanup and leaks the directory forever. This owns the single scratch
// root and a conservative sweep that reclaims only provably abandoned peers: a directory
// is stale when it has outlived the TTL, or when its recorded owner process is gone. A
// young directory with a live owner (an in-flight ceremony) is never reclaimed.
internal static class ScratchWorkspace
{
    internal const string NoindexRootName = "stratalint-scratch.noindex";
    internal const string OwnerMarkerName = ".stratalint-owner";

    internal static readonly TimeSpan DefaultStaleAfter = TimeSpan.FromHours(24);

    // The flat prefixes the (currently frozen) ceremony controllers still create directly
    // under the temp roots. "stratalint-conservative-" also covers the replay and bundle
    // variants. Once the controllers route through Reserve these are only legacy residue.
    internal static readonly ImmutableArray<string> LegacyPrefixes =
    [
        "stratalint-c0-renew-",
        "stratalint-conservative-",
    ];

    internal static string NoindexRoot => Path.Combine(Path.GetTempPath(), NoindexRootName);

    // Reclaim abandoned scratch directories under every known temp root, then reserve a
    // fresh owned directory for `kind` under the Spotlight-excluded scratch root.
    internal static string Reserve(string kind)
    {
        ArgumentException.ThrowIfNullOrEmpty(kind);
        SweepStale();
        Directory.CreateDirectory(NoindexRoot);
        var directory = Path.Combine(NoindexRoot, kind + "-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(directory);
        File.WriteAllText(
            Path.Combine(directory, OwnerMarkerName),
            Environment.ProcessId.ToString(CultureInfo.InvariantCulture) + "\n",
            new UTF8Encoding(false));
        return directory;
    }

    // Production entry point: sweep the real temp roots with the real clock and process table.
    internal static void SweepStale()
    {
        var roots = new[] { Path.GetTempPath(), "/tmp" }
            .Where(Directory.Exists)
            .Select(Path.GetFullPath)
            .Distinct(StringComparer.Ordinal);
        Sweep(
            roots,
            LegacyPrefixes,
            NoindexRootName,
            TimeProvider.System.GetUtcNow(),
            DefaultStaleAfter,
            ProcessIsAlive);
    }

    // Best-effort, idempotent removal of stale scratch directories. Peers matching a legacy
    // prefix are judged directly; the single scratch root is preserved and only its stale
    // children are reclaimed. A directory that cannot be removed is left for the next sweep.
    internal static void Sweep(
        IEnumerable<string> roots,
        IReadOnlyList<string> prefixes,
        string noindexRootName,
        DateTimeOffset now,
        TimeSpan staleAfter,
        Func<int, bool> processIsAlive)
    {
        ArgumentNullException.ThrowIfNull(roots);
        ArgumentNullException.ThrowIfNull(prefixes);
        ArgumentNullException.ThrowIfNull(processIsAlive);
        foreach (var root in roots)
        {
            if (!Directory.Exists(root)) continue;
            foreach (var directory in Directory.EnumerateDirectories(root))
            {
                var name = Path.GetFileName(directory);
                if (string.Equals(name, noindexRootName, StringComparison.Ordinal))
                {
                    foreach (var child in Directory.EnumerateDirectories(directory))
                    {
                        if (IsStale(new DirectoryInfo(child), now, staleAfter, processIsAlive))
                        {
                            TryDelete(child);
                        }
                    }

                    continue;
                }

                if (prefixes.Any(prefix => name.StartsWith(prefix, StringComparison.Ordinal))
                    && IsStale(new DirectoryInfo(directory), now, staleAfter, processIsAlive))
                {
                    TryDelete(directory);
                }
            }
        }
    }

    // A directory is stale when it has outlived the TTL (no ceremony runs anywhere near that
    // long, so a live owner here is a recycled pid) or when its recorded owner is not alive.
    // Young directories with a live owner, or with no readable owner marker, are kept.
    internal static bool IsStale(
        DirectoryInfo directory,
        DateTimeOffset now,
        TimeSpan staleAfter,
        Func<int, bool> processIsAlive)
    {
        ArgumentNullException.ThrowIfNull(directory);
        ArgumentNullException.ThrowIfNull(processIsAlive);
        if (!directory.Exists) return false;
        if (now.UtcDateTime - directory.LastWriteTimeUtc > staleAfter) return true;
        return ReadOwnerProcessId(directory) is int owner && !processIsAlive(owner);
    }

    private static int? ReadOwnerProcessId(DirectoryInfo directory)
    {
        var marker = Path.Combine(directory.FullName, OwnerMarkerName);
        if (!File.Exists(marker)) return null;
        try
        {
            return int.TryParse(
                File.ReadAllText(marker).Trim(),
                NumberStyles.Integer,
                CultureInfo.InvariantCulture,
                out var owner)
                ? owner
                : null;
        }
        catch (IOException)
        {
            return null;
        }
        catch (UnauthorizedAccessException)
        {
            return null;
        }
    }

    private static bool ProcessIsAlive(int processId)
    {
        if (processId <= 0) return false;
        try
        {
            using var process = Process.GetProcessById(processId);
            return !process.HasExited;
        }
        catch (ArgumentException)
        {
            return false;
        }
        catch (InvalidOperationException)
        {
            return false;
        }
    }

    private static void TryDelete(string directory)
    {
        try
        {
            Directory.Delete(directory, recursive: true);
        }
        catch (IOException)
        {
        }
        catch (UnauthorizedAccessException)
        {
        }
    }
}
