using System.Collections.Immutable;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

// IngestCommand 的账本原子写入一族:ApplyLedgerUpdatesAtomically / ReadLedgerFiles /
// PruneEmptyLedgerDirectories / RollbackLedgerUpdates / AddCasObjects / WriteCasObjects。
//
// 余量:宿主原 786 行,是全仓离 SL-003 的 800 行硬线最近的文件(余量 14)。
// 该类本就是 internal static partial,切分不动类声明。
// 注:这是**生产代码**,不在「拆项目与测试项目」原判据内;动它的理由是余量本身 ——
// 本会话已实证撞线会当场挡住 PR(#5433 把 752 行加到 903 行被判红)。

internal static partial class IngestCommand
{
    internal static void ApplyLedgerUpdatesAtomically(
        string repositoryRoot,
        RawRepositorySnapshot current,
        ImmutableArray<LedgerUpdate> updates,
        Action<string, string>? commit = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(current);
        if (updates.Length == 0)
        {
            return;
        }

        var root = Path.GetFullPath(repositoryRoot);
        var expected = current.Entries
            .Where(static entry => IsLedgerPath(entry.Path))
            .ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        var actual = ReadLedgerFiles(root);
        if (expected.Keys.Except(actual.Keys, StringComparer.Ordinal).Any())
        {
            throw new InvalidOperationException(
                "ledger went missing between read and write; aborting to avoid a lost update");
        }

        if (actual.Keys.Except(expected.Keys, StringComparer.Ordinal).Any()
            || expected.Any(pair => !pair.Value.Bytes.AsSpan().SequenceEqual(
                actual[pair.Key].AsSpan())))
        {
            throw new InvalidOperationException(
                "ledger changed under us between read and write; aborting to avoid a lost update");
        }

        var originals = updates.ToDictionary(
            static update => update.Path,
            update => actual.TryGetValue(update.Path, out var bytes)
                ? (ImmutableArray<byte>?)bytes
                : null,
            StringComparer.Ordinal);
        var touched = new List<string>(updates.Length);
        try
        {
            foreach (var update in updates
                         .OrderBy(static update => update.DurabilityOrder)
                         .ThenBy(static update => update.Path, StringComparer.Ordinal))
            {
                touched.Add(update.Path);
                var outputPath = Path.Combine(
                    root,
                    update.Path.Replace('/', Path.DirectorySeparatorChar));
                if (update.Bytes is null)
                {
                    File.Delete(outputPath);
                    continue;
                }

                Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
                ReplaceLedgerAtomically(outputPath, update.Bytes.Value.AsSpan(), commit);
            }

            PruneEmptyLedgerDirectories(root, updates);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            RollbackLedgerUpdates(root, touched, originals, exception);
            throw;
        }
    }

    private static bool IsLedgerPath(string path) =>
        string.Equals(path, BackfillInventoryLoader.RelativePath, StringComparison.Ordinal)
        || BackfillInventoryLoader.IsCanonicalPath(path);

    private static Dictionary<string, ImmutableArray<byte>> ReadLedgerFiles(string root)
    {
        var result = new Dictionary<string, ImmutableArray<byte>>(StringComparer.Ordinal);
        AddIfFile(BackfillInventoryLoader.RelativePath);
        var directory = Path.Combine(
            root,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar));
        if (Directory.Exists(directory))
        {
            foreach (var path in Directory.EnumerateFiles(directory, "*", SearchOption.AllDirectories))
            {
                Add(Path.GetRelativePath(root, path).Replace(Path.DirectorySeparatorChar, '/'), path);
            }
        }

        return result;

        void AddIfFile(string relativePath)
        {
            var fullPath = Path.Combine(
                root,
                relativePath.Replace('/', Path.DirectorySeparatorChar));
            if (File.Exists(fullPath))
            {
                Add(relativePath, fullPath);
            }
        }

        void Add(string relativePath, string fullPath) =>
            result.Add(relativePath, ImmutableArray.CreateRange(File.ReadAllBytes(fullPath)));
    }

    private static void PruneEmptyLedgerDirectories(
        string root,
        IEnumerable<LedgerUpdate> updates)
    {
        var ledgerRoot = Path.GetFullPath(Path.Combine(
            root,
            BackfillInventoryLoader.RootPath.Replace('/', Path.DirectorySeparatorChar)));
        var ledgerRootPrefix = ledgerRoot.EndsWith(Path.DirectorySeparatorChar)
            ? ledgerRoot
            : ledgerRoot + Path.DirectorySeparatorChar;
        var directories = new HashSet<string>(StringComparer.Ordinal);
        foreach (var update in updates.Where(static update =>
                     update.Bytes is null
                     && update.Path.StartsWith(BackfillInventoryLoader.RootPath, StringComparison.Ordinal)
                     && BackfillInventoryLoader.IsCanonicalPath(update.Path)))
        {
            var outputPath = Path.GetFullPath(Path.Combine(
                root,
                update.Path.Replace('/', Path.DirectorySeparatorChar)));
            for (var directory = Path.GetDirectoryName(outputPath);
                 directory is not null
                 && directory.StartsWith(ledgerRootPrefix, StringComparison.Ordinal);
                 directory = Path.GetDirectoryName(directory))
            {
                directories.Add(directory);
            }
        }

        foreach (var directory in directories
                     .OrderByDescending(static path => path.Length)
                     .ThenBy(static path => path, StringComparer.Ordinal))
        {
            if (Directory.Exists(directory)
                && !Directory.EnumerateFileSystemEntries(directory).Any())
            {
                Directory.Delete(directory);
            }
        }
    }

    private static void RollbackLedgerUpdates(
        string root,
        IEnumerable<string> touched,
        IReadOnlyDictionary<string, ImmutableArray<byte>?> originals,
        Exception writeFailure)
    {
        var rollbackFailures = new List<Exception>();
        foreach (var path in touched.Reverse())
        {
            var outputPath = Path.Combine(
                root,
                path.Replace('/', Path.DirectorySeparatorChar));
            try
            {
                if (originals[path] is { } bytes)
                {
                    Directory.CreateDirectory(Path.GetDirectoryName(outputPath)!);
                    ReplaceLedgerAtomically(outputPath, bytes.AsSpan());
                }
                else
                {
                    File.Delete(outputPath);
                }
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                rollbackFailures.Add(exception);
            }
        }

        if (rollbackFailures.Count > 0)
        {
            throw new AggregateException(
                "ledger write failed and rollback was incomplete",
                new[] { writeFailure }.Concat(rollbackFailures));
        }
    }

    private static RawRepositorySnapshot AddCasObjects(
        RawRepositorySnapshot snapshot,
        ImmutableArray<DigestionCasObject> casObjects)
    {
        var entries = snapshot.Entries.ToDictionary(static entry => entry.Path, StringComparer.Ordinal);
        foreach (var item in casObjects)
        {
            if (entries.TryGetValue(item.RelativePath, out var existing))
            {
                if (!existing.Bytes.AsSpan().SequenceEqual(item.Bytes.AsSpan()))
                {
                    throw new InvalidOperationException(
                        $"CAS path already contains different bytes: {item.RelativePath}");
                }

                continue;
            }

            entries.Add(item.RelativePath, new RawRepositoryEntry(item.RelativePath, item.Bytes));
        }

        return RawRepositorySnapshot.Create(entries.Values.OrderBy(
            static entry => entry.Path,
            StringComparer.Ordinal));
    }

    private static ImmutableArray<string> WriteCasObjects(
        string repositoryRoot,
        ImmutableArray<DigestionCasObject> casObjects)
    {
        var pending = new List<(DigestionCasObject Object, string FullPath)>();
        var root = Path.GetFullPath(repositoryRoot);
        foreach (var item in casObjects)
        {
            var fullPath = Path.Combine(
                root,
                item.RelativePath.Replace('/', Path.DirectorySeparatorChar));
            if (File.Exists(fullPath))
            {
                if (!File.ReadAllBytes(fullPath).AsSpan().SequenceEqual(item.Bytes.AsSpan()))
                {
                    throw new InvalidOperationException(
                        $"CAS path already contains different bytes: {item.RelativePath}");
                }

                continue;
            }

            pending.Add((item, fullPath));
        }

        var created = ImmutableArray.CreateBuilder<string>(pending.Count);
        try
        {
            foreach (var (item, fullPath) in pending)
            {
                Directory.CreateDirectory(Path.GetDirectoryName(fullPath)!);
                using var output = new FileStream(
                    fullPath,
                    FileMode.CreateNew,
                    FileAccess.Write,
                    FileShare.None);
                created.Add(fullPath);
                output.Write(item.Bytes.AsSpan());
                output.Flush(flushToDisk: true);
            }
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            RollbackCasObjects(created, exception);
            throw;
        }

        return created.ToImmutable();
    }

    internal static void ReplaceLedgerAtomically(
        string outputPath,
        ReadOnlySpan<byte> bytes,
        Action<string, string>? commit = null)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(outputPath);
        var target = Path.GetFullPath(outputPath);
        var directory = Path.GetDirectoryName(target)
            ?? throw new InvalidOperationException("ledger output path has no parent directory");
        var pending = Path.Combine(
            directory,
            $".{Path.GetFileName(target)}.{Guid.NewGuid():N}.tmp");
        try
        {
            using (var output = new FileStream(
                       pending,
                       FileMode.CreateNew,
                       FileAccess.Write,
                       FileShare.None))
            {
                output.Write(bytes);
                output.Flush(flushToDisk: true);
            }

            commit ??= static (source, destination) =>
                File.Move(source, destination, overwrite: true);
            commit(pending, target);
        }
        finally
        {
            File.Delete(pending);
        }
    }

    private static void RollbackCasObjects(
        IEnumerable<string> createdPaths,
        Exception writeFailure)
    {
        var rollbackFailures = new List<Exception>();
        foreach (var path in createdPaths.Reverse())
        {
            try
            {
                File.Delete(path);
            }
            catch (Exception exception) when (exception is not OutOfMemoryException)
            {
                rollbackFailures.Add(exception);
            }
        }

        if (rollbackFailures.Count > 0)
        {
            throw new AggregateException(
                "CAS write failed and rollback was incomplete",
                new[] { writeFailure }.Concat(rollbackFailures));
        }
    }
}
