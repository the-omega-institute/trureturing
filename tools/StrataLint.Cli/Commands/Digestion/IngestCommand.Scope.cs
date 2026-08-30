using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private const string ImplementationPath =
        "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs";

    private static RawChangeSet IngestChanges(
        RawChangeSet repositoryChanges,
        RawRepositorySnapshot current,
        RawRepositorySnapshot candidate,
        BackfillInventoryDocument candidateDocument,
        ImmutableArray<DigestionCasObject> casObjects)
    {
        var changes = repositoryChanges.Entries.ToDictionary(
            static entry => entry.Path.Value,
            static entry => entry.Kind,
            StringComparer.Ordinal);
        var currentPaths = current.Entries.Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var candidatePaths = candidate.Entries.Select(static entry => entry.Path)
            .ToHashSet(StringComparer.Ordinal);
        var operationPaths = LedgerUpdates(current, candidate)
            .Select(static update => update.Path)
            .Concat(casObjects.Select(static item => item.RelativePath))
            .ToHashSet(StringComparer.Ordinal);
        var touchedSourceIds = candidateDocument.RequireDigestionSources()
            .Where(source => operationPaths.Any(path => path.StartsWith(
                $"{BackfillInventoryLoader.RootPath}{source.SourceId}/",
                StringComparison.Ordinal)))
            .Select(static source => source.SourceId)
            .ToHashSet(StringComparer.Ordinal);
        operationPaths.UnionWith(candidateDocument.RequireDigestionSources()
            .Where(source => touchedSourceIds.Contains(source.SourceId))
            .Select(static source => source.SourcePath));

        foreach (var path in operationPaths)
        {
            if (changes.ContainsKey(path))
            {
                continue;
            }

            changes.Add(
                path,
                !currentPaths.Contains(path)
                    ? RawChangeKind.Added
                    : !candidatePaths.Contains(path)
                        ? RawChangeKind.Deleted
                        : RawChangeKind.Modified);
        }

        return RawChangeSet.CreateWithKinds(changes
            .OrderBy(static entry => entry.Key, StringComparer.Ordinal)
            .Select(static entry => (Path: entry.Key, Kind: entry.Value)));
    }
}
