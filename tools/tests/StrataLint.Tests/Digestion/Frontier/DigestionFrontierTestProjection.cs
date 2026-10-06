using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Tests;

internal static class DigestionFrontierTestProjection
{
    internal static DigestionFrontierProjection Create(
        DigestionLedgerEvaluation evaluation,
        IReadOnlyDictionary<string, string>? contentKinds = null,
        ImmutableArray<string> acknowledgedStale = default)
    {
        var sources = evaluation.Entries
            .GroupBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
            .Select(group => new DigestionLedgerSource(
                group.Key,
                group.First().Entry.SourcePath,
                group.First().Entry.Atomizer,
                acknowledgedStale.IsDefault
                    ? []
                    : acknowledgedStale.Where(id => group.Any(item => item.Entry.AtomId == id))
                        .ToImmutableArray(),
                GenreRegistryProjection.Available(GenreRegistryCheck.NoGenreRegistry),
                group.Select(static item => item.Entry).ToImmutableArray()))
            .ToImmutableArray();
        var document = BackfillInventoryDocument.Create(sources, []);
        return DigestionFrontierProjection.Create(
            document,
            evaluation,
            contentKinds ?? new Dictionary<string, string>(StringComparer.Ordinal));
    }
}
