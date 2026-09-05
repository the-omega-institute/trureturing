using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class FrozenLedgerPublication
{
    internal static void PublishSnapshot(
        string repositoryRoot,
        string ledgerDirectory,
        IEnumerable<RepositoryFile> targetFiles,
        ImmutableArray<RepositoryFile> expectedBaselineFiles,
        IEnumerable<DagLedgerFileEvent> freezesToPublish,
        IEnumerable<RepoPath> selectorsToDelete,
        string command)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentException.ThrowIfNullOrWhiteSpace(ledgerDirectory);
        ArgumentNullException.ThrowIfNull(targetFiles);
        ArgumentNullException.ThrowIfNull(freezesToPublish);
        ArgumentNullException.ThrowIfNull(selectorsToDelete);
        ArgumentException.ThrowIfNullOrWhiteSpace(command);

        var planned = targetFiles
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        if (planned.Select(static file => file.Path).Distinct().Count() != planned.Length)
        {
            throw new InvalidOperationException("published frozen ledger contains duplicate paths");
        }

        var stateChanges = BuildStateChanges(freezesToPublish, selectorsToDelete);
        var lockPath = Path.Combine(ledgerDirectory, ".ledger-write.lock");
        using var publicationLock = AcquirePublicationLock(lockPath);
        if (!LedgerDirectoryMatches(ledgerDirectory, expectedBaselineFiles))
        {
            throw new InvalidOperationException(
                $"accepted event files changed while {command} was validating them");
        }

        var stateBackups = stateChanges.ToDictionary(
            static change => change.ModulePath,
            change => FrozenStateWriter.ReadCurrentBytes(repositoryRoot, change.ModulePath));
        ReapStaleStagingDirectories(ledgerDirectory);
        var baselineByPath = expectedBaselineFiles.ToDictionary(static file => file.Path);
        var plannedByPath = planned.ToDictionary(static file => file.Path);
        var changedFiles = planned
            .Where(file => !baselineByPath.TryGetValue(file.Path, out var baseline)
                || !file.RawBytes.AsSpan().SequenceEqual(baseline.RawBytes.AsSpan()))
            .ToImmutableArray();
        var displacedFiles = expectedBaselineFiles
            .Where(file => !plannedByPath.TryGetValue(file.Path, out var target)
                || !file.RawBytes.AsSpan().SequenceEqual(target.RawBytes.AsSpan()))
            .OrderBy(static file => file.Path.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        var stagingDirectory = Path.Combine(
            ledgerDirectory,
            $".ledger-stage-{Guid.NewGuid():N}");
        var newDirectory = Path.Combine(stagingDirectory, "new");
        var oldDirectory = Path.Combine(stagingDirectory, "old");
        var published = new Stack<string>();
        var displaced = new Stack<(string Staged, string Original)>();
        try
        {
            Directory.CreateDirectory(newDirectory);
            Directory.CreateDirectory(oldDirectory);
            StageFiles(changedFiles, newDirectory);
            foreach (var file in displacedFiles)
            {
                var original = Path.Combine(ledgerDirectory, Path.GetFileName(file.Path.Value));
                var staged = Path.Combine(oldDirectory, Path.GetFileName(file.Path.Value));
                File.Move(original, staged);
                displaced.Push((staged, original));
            }

            foreach (var file in changedFiles)
            {
                var fileName = Path.GetFileName(file.Path.Value);
                var staged = Path.Combine(newDirectory, fileName);
                var final = Path.Combine(ledgerDirectory, fileName);
                File.Move(staged, final);
                published.Push(final);
            }

            foreach (var change in stateChanges)
            {
                if (change.StatementId is null)
                {
                    _ = FrozenStateWriter.Delete(repositoryRoot, change.ModulePath);
                }
                else
                {
                    _ = FrozenStateWriter.Write(
                        repositoryRoot,
                        change.ModulePath,
                        change.StatementId);
                }
            }

            Directory.Delete(stagingDirectory, recursive: true);
        }
        catch (Exception publicationFailure)
        {
            Exception? rollbackFailure = null;
            try
            {
                RollbackEvents(published, displaced);
            }
            catch (Exception exception) when (
                exception is IOException or UnauthorizedAccessException)
            {
                rollbackFailure = exception;
            }

            try
            {
                foreach (var (path, previousBytes) in stateBackups)
                {
                    FrozenStateWriter.Restore(repositoryRoot, path, previousBytes);
                }
            }
            catch (Exception exception) when (
                exception is IOException or UnauthorizedAccessException)
            {
                rollbackFailure = rollbackFailure is null
                    ? exception
                    : new AggregateException(rollbackFailure, exception);
            }

            CleanupStagingDirectory(stagingDirectory);
            if (rollbackFailure is not null)
            {
                throw new IOException(
                    "Frozen ledger publication failed and rollback was incomplete.",
                    new AggregateException(publicationFailure, rollbackFailure));
            }

            throw;
        }
    }

    private static ImmutableArray<FrozenStateChange> BuildStateChanges(
        IEnumerable<DagLedgerFileEvent> freezesToPublish,
        IEnumerable<RepoPath> selectorsToDelete)
    {
        var changes = freezesToPublish.Select(static freeze =>
        {
            if (freeze.EventType != "Freeze")
            {
                throw new InvalidOperationException(
                    "Frozen state can only mirror published Freeze events.");
            }

            var statementId = freeze.Payload.GetProperty("statement_id").GetString()
                ?? throw new FormatException("Freeze statement_id is null.");
            return new FrozenStateChange(
                freeze.DescriptorPath,
                StatementId.Create(statementId));
        }).Concat(selectorsToDelete.Select(static path => new FrozenStateChange(path, null)))
            .OrderBy(static change => change.ModulePath.Value, StringComparer.Ordinal)
            .ToImmutableArray();
        if (changes.Select(static change => change.ModulePath).Distinct().Count() != changes.Length)
        {
            throw new InvalidOperationException(
                "Frozen ledger publication contains duplicate state selectors.");
        }

        return changes;
    }

    private static void StageFiles(
        IEnumerable<RepositoryFile> files,
        string stagingDirectory)
    {
        foreach (var file in files)
        {
            var stagedPath = Path.Combine(stagingDirectory, Path.GetFileName(file.Path.Value));
            using var stream = new FileStream(
                stagedPath,
                FileMode.CreateNew,
                FileAccess.Write,
                FileShare.None);
            stream.Write(file.RawBytes.AsSpan());
            stream.Flush(flushToDisk: true);
        }
    }

    private static void RollbackEvents(
        Stack<string> published,
        Stack<(string Staged, string Original)> displaced)
    {
        while (published.TryPop(out var path))
        {
            File.Delete(path);
        }

        while (displaced.TryPop(out var item))
        {
            if (File.Exists(item.Staged))
            {
                File.Move(item.Staged, item.Original);
            }
        }
    }

    private static bool LedgerDirectoryMatches(
        string directory,
        ImmutableArray<RepositoryFile> expectedFiles)
    {
        var actual = DagLedgerCommandPreparation.ReadLedgerDirectoryFiles(directory);
        if (actual.Length != expectedFiles.Length)
        {
            return false;
        }

        var expectedByPath = expectedFiles.ToDictionary(static file => file.Path);
        return actual.All(file => expectedByPath.TryGetValue(file.Path, out var expected)
            && file.RawBytes.AsSpan().SequenceEqual(expected.RawBytes.AsSpan()));
    }

    private static FileStream AcquirePublicationLock(string lockPath)
    {
        try
        {
            return new FileStream(
                lockPath,
                FileMode.OpenOrCreate,
                FileAccess.ReadWrite,
                FileShare.None);
        }
        catch (Exception failure) when (failure is IOException or UnauthorizedAccessException)
        {
            throw new IOException(
                $"Another frozen-ledger publication owns the writer lock {lockPath}.",
                failure);
        }
    }

    private static void ReapStaleStagingDirectories(string directory)
    {
        foreach (var stagingDirectory in Directory.EnumerateDirectories(
            directory,
            ".ledger-stage-*",
            SearchOption.TopDirectoryOnly))
        {
            Directory.Delete(stagingDirectory, recursive: true);
        }
    }

    private static void CleanupStagingDirectory(string stagingDirectory)
    {
        try
        {
            if (Directory.Exists(stagingDirectory))
            {
                Directory.Delete(stagingDirectory, recursive: true);
            }
        }
        catch (IOException)
        {
        }
        catch (UnauthorizedAccessException)
        {
        }
    }

    private sealed record FrozenStateChange(
        RepoPath ModulePath,
        StatementId? StatementId);
}
