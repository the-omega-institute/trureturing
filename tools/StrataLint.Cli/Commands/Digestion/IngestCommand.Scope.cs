using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static partial class IngestCommand
{
    private const string ImplementationPath =
        "tools/StrataLint.Cli/Commands/Digestion/IngestCommand.cs";

    private static string ParseArguments(IReadOnlyList<string> arguments)
    {
        if (arguments.Count == 2
            && arguments[0] == "--base"
            && !string.IsNullOrWhiteSpace(arguments[1]))
        {
            return arguments[1];
        }

        throw new InvalidOperationException("USAGE: StrataLint ingest --base REV");
    }

    private static RawChangeSet EffectiveChanges(
        RawRepositorySnapshot baseline,
        RawRepositorySnapshot candidate)
    {
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(candidate);
        var baselineByPath = baseline.Entries.ToDictionary(
            static entry => entry.Path,
            StringComparer.Ordinal);
        var candidateByPath = candidate.Entries.ToDictionary(
            static entry => entry.Path,
            StringComparer.Ordinal);
        var paths = baselineByPath.Keys
            .Concat(candidateByPath.Keys)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal);
        var changes = new List<(string Path, RawChangeKind Kind)>();
        foreach (var path in paths)
        {
            var inBaseline = baselineByPath.TryGetValue(path, out var baselineEntry);
            var inCandidate = candidateByPath.TryGetValue(path, out var candidateEntry);
            if (inBaseline
                && inCandidate
                && baselineEntry!.Bytes.AsSpan().SequenceEqual(candidateEntry!.Bytes.AsSpan()))
            {
                continue;
            }

            changes.Add((
                path,
                !inBaseline
                    ? RawChangeKind.Added
                    : !inCandidate
                        ? RawChangeKind.Deleted
                        : RawChangeKind.Modified));
        }

        return RawChangeSet.CreateWithKinds(changes);
    }

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
