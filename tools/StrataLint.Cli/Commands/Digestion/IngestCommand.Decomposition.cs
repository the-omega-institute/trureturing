using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    internal static void ApplyDecompositionAtomically(string root, RawRepositorySnapshot current,
        ImmutableArray<DigestionCasObject> cas, ImmutableArray<LedgerUpdate> updates,
        Func<string, ImmutableArray<DigestionCasObject>, ImmutableArray<string>> writeCas,
        Action<string, RawRepositorySnapshot, ImmutableArray<LedgerUpdate>> applyLedger,
        Action<IEnumerable<string>, Exception> rollbackCas)
    {
        var created = writeCas(root, cas);
        try
        {
            applyLedger(root, current, updates);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            rollbackCas(created, exception);
            throw;
        }
    }

    internal static void ApplyDecompositionAtomically(string root, RawRepositorySnapshot current,
        ImmutableArray<DigestionCasObject> cas, ImmutableArray<LedgerUpdate> updates)
        => ApplyDecompositionAtomically(root, current, cas, updates, WriteCasObjects,
            static (directory, snapshot, changes) => ApplyLedgerUpdatesAtomically(directory, snapshot, changes),
            RollbackCasObjects);
}
