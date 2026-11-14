using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class RetireSourcesCommand
{
    private static void ApplyRetirementAtomically(string root, RawRepositorySnapshot current,
        ImmutableArray<IngestCommand.LedgerUpdate> updates, Action<string, string>? commit,
        Action<string>? beforeArchivePublication, Action requireInputsUnchanged)
    {
        requireInputsUnchanged();
        var published = new List<(string Path, ImmutableArray<byte> Bytes)>();
        try
        {
            foreach (var update in updates.Where(update => update.Bytes is not null).OrderBy(update => update.Path, StringComparer.Ordinal))
            {
                var destination = Path.Combine(root, update.Path);
                Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
                IngestCommand.ReplaceLedgerAtomically(destination, update.Bytes!.Value.AsSpan(), (temporary, target) =>
                {
                    beforeArchivePublication?.Invoke(target);
                    if (commit is null) File.Move(temporary, target, overwrite: false);
                    else commit(temporary, target);
                    published.Add((target, update.Bytes.Value));
                });
            }
            IngestCommand.ApplyLedgerUpdatesAtomically(root, current,
                updates.Where(update => update.Bytes is null).ToImmutableArray());
        }
        catch (Exception failure) when (failure is not OutOfMemoryException)
        {
            var rollbackFailures = new List<Exception>();
            foreach (var (path, bytes) in published.AsEnumerable().Reverse())
                try
                {
                    if (!File.Exists(path)) continue;
                    if (!File.ReadAllBytes(path).AsSpan().SequenceEqual(bytes.AsSpan()))
                        throw new IOException($"ARCHIVE_CHANGED_DURING_ROLLBACK path={path}");
                    File.Delete(path);
                }
                catch (Exception error) when (error is not OutOfMemoryException) { rollbackFailures.Add(error); }
            if (rollbackFailures.Count > 0)
                throw new AggregateException("retirement failed and archive rollback was incomplete", new[] { failure }.Concat(rollbackFailures));
            throw;
        }
    }
}
