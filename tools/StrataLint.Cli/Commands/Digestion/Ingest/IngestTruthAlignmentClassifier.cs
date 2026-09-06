using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class IngestPreservedExistingObserver
{
    internal static ImmutableArray<DigestionIngestObservation> ObserveCurrent(
        BackfillInventoryDocument current,
        BackfillInventoryDocument baseline,
        ImmutableHashSet<string>? sourceIds = null)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        var observations = new HashSet<DigestionIngestObservation>();
        var baselineEntries = Entries(baseline, sourceIds);
        var currentEntries = Entries(current, sourceIds);
        foreach (var item in currentEntries.Values)
        {
            if (!baselineEntries.TryGetValue(item.Entry.AtomId, out var baselineItem)
                || !StatusAuthorityEqual(item, baselineItem))
            {
                observations.Add(new DigestionIngestObservation(
                    item.Entry.AtomId,
                    item.Source.SourceId,
                    "current-vs-base-changed"));
            }
        }

        foreach (var item in baselineEntries.Values.Where(item =>
                     !currentEntries.ContainsKey(item.Entry.AtomId)))
        {
            observations.Add(new DigestionIngestObservation(
                item.Entry.AtomId,
                item.Source.SourceId,
                "removed"));
        }

        var currentSources = Sources(current, sourceIds);
        var baselineSources = Sources(baseline, sourceIds);
        foreach (var (sourceId, source) in currentSources)
        {
            if (!baselineSources.TryGetValue(sourceId, out var baselineSource))
                continue;

            var acknowledgmentChanges = source.AcknowledgedStale
                .Concat(baselineSource.AcknowledgedStale)
                .Distinct(StringComparer.Ordinal)
                .Where(atomId => source.AcknowledgedStale.Contains(atomId, StringComparer.Ordinal)
                    != baselineSource.AcknowledgedStale.Contains(atomId, StringComparer.Ordinal));
            foreach (var atomId in acknowledgmentChanges)
            {
                observations.Add(new DigestionIngestObservation(
                    atomId,
                    sourceId,
                    "acknowledged-stale-changed"));
            }

            if (!Equals(source.GenreRegistryCheck, baselineSource.GenreRegistryCheck))
            {
                foreach (var atomId in source.Entries.Select(static entry => entry.AtomId)
                             .Concat(baselineSource.Entries.Select(static entry => entry.AtomId))
                             .Distinct(StringComparer.Ordinal))
                {
                    observations.Add(new DigestionIngestObservation(
                        atomId,
                        sourceId,
                        "genre-projection-changed"));
                }
            }
        }

        return Sort(observations);
    }

    internal static ImmutableArray<DigestionIngestObservation> ObservePlanned(
        BackfillInventoryDocument current,
        BackfillInventoryDocument planned,
        ImmutableHashSet<string>? sourceIds = null)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(planned);
        var observations = new HashSet<DigestionIngestObservation>();
        var currentEntries = Entries(current, sourceIds);
        var plannedEntries = Entries(planned, sourceIds);
        foreach (var item in currentEntries.Values)
        {
            var entry = item.Entry;
            if (!plannedEntries.TryGetValue(entry.AtomId, out var plannedItem))
            {
                observations.Add(new DigestionIngestObservation(
                    entry.AtomId,
                    item.Source.SourceId,
                    entry.CoverageGids.IsEmpty ? "planned-rewrite" : "covered-disappeared"));
                continue;
            }

            if (!entry.CoverageGids.IsEmpty && plannedItem.Entry.CoverageGids.IsEmpty)
            {
                observations.Add(new DigestionIngestObservation(
                    entry.AtomId,
                    item.Source.SourceId,
                    "covered-cleared"));
            }
            if (!StatusAuthorityEqual(item, plannedItem))
            {
                observations.Add(new DigestionIngestObservation(
                    entry.AtomId,
                    item.Source.SourceId,
                    "planned-rewrite"));
            }
        }

        return Sort(observations);
    }

    internal static ImmutableArray<DigestionIngestObservation> ObserveAuthorityChanges(
        BackfillInventoryDocument current,
        BackfillInventoryDocument baseline,
        DigestionLedgerAlignment alignment,
        DigestionEvaluationScope scope,
        RawChangeSet repositoryChanges,
        ImmutableHashSet<string>? sourceIds = null)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(alignment);
        ArgumentNullException.ThrowIfNull(repositoryChanges);
        var resolvedChanges = DigestionEvaluationScopes.ResolveChanges(scope, repositoryChanges);
        var changed = DigestionStatusEvaluator.StatusAuthorityChangedAtomIds(
            current,
            baseline,
            resolvedChanges,
            alignment,
            sourceIds);
        return Sort(current.RequireDigestionEntries()
            .Where(entry => (sourceIds is null || sourceIds.Contains(entry.SourceId))
                && changed.Contains(entry.AtomId))
            .Select(static entry => new DigestionIngestObservation(
                entry.AtomId,
                entry.SourceId,
                "current-vs-base-changed")));
    }

    internal static ImmutableArray<DigestionIngestObservation> Combine(
        params IEnumerable<DigestionIngestObservation>[] groups) =>
        Sort(groups.SelectMany(static group => group));

    private static Dictionary<string, StatusAuthorityEntry> Entries(
        BackfillInventoryDocument document,
        ImmutableHashSet<string>? sourceIds) =>
        document.RequireDigestionSources()
            .Where(source => sourceIds is null || sourceIds.Contains(source.SourceId))
            .SelectMany(source => source.Entries.Select(entry => new StatusAuthorityEntry(source, entry)))
            .ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);

    private static Dictionary<string, DigestionLedgerSource> Sources(
        BackfillInventoryDocument document,
        ImmutableHashSet<string>? sourceIds) =>
        document.RequireDigestionSources()
            .Where(source => sourceIds is null || sourceIds.Contains(source.SourceId))
            .ToDictionary(static source => source.SourceId, StringComparer.Ordinal);

    private static bool StatusAuthorityEqual(StatusAuthorityEntry left, StatusAuthorityEntry right) =>
        BackfillInventoryWriter.WriteStatusAuthorityIdentity(left.Source, left.Entry)
            .AsSpan()
            .SequenceEqual(
                BackfillInventoryWriter.WriteStatusAuthorityIdentity(right.Source, right.Entry).AsSpan());

    private static ImmutableArray<DigestionIngestObservation> Sort(
        IEnumerable<DigestionIngestObservation> observations) =>
        observations
            .Distinct()
            .OrderBy(static item => item.AtomId, StringComparer.Ordinal)
            .ThenBy(static item => item.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.Kind, StringComparer.Ordinal)
            .ToImmutableArray();

    private sealed record StatusAuthorityEntry(
        DigestionLedgerSource Source,
        DigestionLedgerEntry Entry);
}
