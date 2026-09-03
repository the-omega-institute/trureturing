using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    // expand phase (L2a): one-off L2b migration tool; removed in L2c after the L2b data migration
    internal static CommandResult RunCoverageMigration(
        string repositoryRoot,
        IRepositoryGateway repository,
        ILeanReportSource leanReportSource,
        IReadOnlyList<string> arguments)
    {
        ArgumentException.ThrowIfNullOrWhiteSpace(repositoryRoot);
        ArgumentNullException.ThrowIfNull(repository);
        ArgumentNullException.ThrowIfNull(leanReportSource);
        ArgumentNullException.ThrowIfNull(arguments);
        try
        {
            if (arguments.Count != 0)
            {
                throw new FormatException("migrate-digestion-coverage accepts no arguments");
            }

            var currentRaw = repository.ReadCurrent();
            var current = Decode(currentRaw);
            var lean = ValidateLean(current, leanReportSource.Load(current));
            var first = DigestionCoverageSchemaMigrator.Migrate(current, lean);
            var finalRaw = ReplaceCoverageMigrationAtoms(currentRaw, first.AtomFiles);
            var finalSnapshot = Decode(finalRaw);
            var second = DigestionCoverageSchemaMigrator.Migrate(finalSnapshot, lean);
            var secondPassChangedPaths = first.AtomFiles
                .Where(pair => !second.AtomFiles.TryGetValue(pair.Key, out var bytes)
                    || !pair.Value.AsSpan().SequenceEqual(bytes.AsSpan()))
                .Select(static pair => pair.Key)
                .Concat(second.AtomFiles.Keys.Where(path => !first.AtomFiles.ContainsKey(path)))
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal)
                .ToArray();
            if (secondPassChangedPaths.Length != 0)
            {
                throw new InvalidOperationException(
                    $"coverage migration is not byte-idempotent: {secondPassChangedPaths.Length} "
                    + "file(s) changed: "
                    + string.Join(", ", secondPassChangedPaths));
            }

            var currentEntries = currentRaw.Entries.ToDictionary(
                static entry => entry.Path,
                StringComparer.Ordinal);
            var updates = first.AtomFiles
                .Where(pair => !currentEntries.TryGetValue(pair.Key, out var existing)
                    || !existing.Bytes.AsSpan().SequenceEqual(pair.Value.AsSpan()))
                .OrderBy(static pair => pair.Key, StringComparer.Ordinal)
                .Select(static pair => new LedgerUpdate(pair.Key, pair.Value))
                .ToImmutableArray();
            ApplyLedgerUpdatesAtomically(repositoryRoot, currentRaw, updates);
            return new CommandResult(
                true,
                "COVERAGE_MIGRATION "
                    + $"atoms={first.AtomFiles.Count} "
                    + $"source_bindings_validated={first.SourceBindingsValidated} "
                    + $"relationships_before={first.RelationshipsBefore} "
                    + $"relationships_after={first.RelationshipsAfter} "
                    + $"resolved_targets={first.ResolvedTargets} "
                    + $"null_targets={first.NullTargets} "
                    + $"changed_files={updates.Length} "
                    + $"second_pass_changed_files={secondPassChangedPaths.Length}\n",
                string.Empty);
        }
        catch (Exception exception) when (exception is not OutOfMemoryException)
        {
            return new CommandResult(
                false,
                string.Empty,
                $"COVERAGE_MIGRATION_INVALID {exception.Message}\n");
        }
    }

    private static RawRepositorySnapshot ReplaceCoverageMigrationAtoms(
        RawRepositorySnapshot current,
        ImmutableDictionary<string, ImmutableArray<byte>> replacements)
    {
        var remaining = replacements.Keys.ToHashSet(StringComparer.Ordinal);
        var entries = current.Entries.Select(entry =>
        {
            if (!replacements.TryGetValue(entry.Path, out var replacement))
            {
                return entry;
            }

            remaining.Remove(entry.Path);
            return new RawRepositoryEntry(entry.Path, replacement, entry.GitBlobOid);
        }).ToArray();
        if (remaining.Count != 0)
        {
            throw new InvalidOperationException(
                "coverage migration produced unknown atom paths: "
                + string.Join(", ", remaining.Order(StringComparer.Ordinal)));
        }

        return RawRepositorySnapshot.Create(entries);
    }
}
