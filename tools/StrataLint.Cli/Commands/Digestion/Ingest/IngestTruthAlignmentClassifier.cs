using StrataLint.Engine;

namespace StrataLint.Cli;

internal enum LeanReportInputState
{
    Unchanged,
    Changed,
}

internal sealed record IngestTruthAlignmentClassification(bool IsUncoveredOnly, string? Witness)
{
    internal static IngestTruthAlignmentClassification UncoveredOnly { get; } = new(true, null);

    internal static IngestTruthAlignmentClassification TruthAlignmentRequired(string witness) =>
        new(false, witness);
}

internal static class IngestTruthAlignmentClassifier
{
    private static readonly DigestionStatus ResidualOpen = new(
        DigestionMigrationState.Residual,
        DigestionTruthState.Open);

    internal static IngestTruthAlignmentClassification ClassifyCurrent(
        LeanReportInputState reportInputState,
        BackfillInventoryDocument current,
        BackfillInventoryDocument baseline)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        if (reportInputState == LeanReportInputState.Changed)
        {
            return IngestTruthAlignmentClassification.TruthAlignmentRequired(
                "Lean report input closure changed");
        }

        var baselineEntries = StatusAuthorityEntries(baseline);
        var currentEntries = StatusAuthorityEntries(current);
        foreach (var item in currentEntries.Values.OrderBy(
                     static item => item.Entry.AtomId,
                     StringComparer.Ordinal))
        {
            var entry = item.Entry;
            if (!baselineEntries.TryGetValue(entry.AtomId, out var baselineItem))
            {
                if (ValidateNewEntry(entry) is { } witness)
                {
                    return IngestTruthAlignmentClassification.TruthAlignmentRequired(witness);
                }

                continue;
            }

            if (!StatusAuthorityEqual(item, baselineItem))
            {
                return IngestTruthAlignmentClassification.TruthAlignmentRequired(
                    $"existing entry {entry.AtomId} changed status-authority inputs");
            }
        }

        var removedEntry = baselineEntries.Keys
            .Except(currentEntries.Keys, StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .FirstOrDefault();
        if (removedEntry is not null)
        {
            return IngestTruthAlignmentClassification.TruthAlignmentRequired(
                $"existing entry {removedEntry} removed");
        }

        return IngestTruthAlignmentClassification.UncoveredOnly;
    }

    internal static IngestTruthAlignmentClassification ClassifyPlanned(
        BackfillInventoryDocument current,
        BackfillInventoryDocument baseline,
        BackfillInventoryDocument planned,
        DigestionEvaluationScope scope,
        RawChangeSet changes)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(planned);
        ArgumentNullException.ThrowIfNull(changes);
        var currentEntries = StatusAuthorityEntries(current);

        foreach (var item in StatusAuthorityEntries(planned).Values
                     .OrderBy(static item => item.Entry.AtomId, StringComparer.Ordinal))
        {
            var entry = item.Entry;
            if (currentEntries.TryGetValue(entry.AtomId, out var currentEntry))
            {
                if (!StatusAuthorityEqual(item, currentEntry))
                {
                    return IngestTruthAlignmentClassification.TruthAlignmentRequired(
                        $"planned rewrite of existing entry {entry.AtomId}");
                }

                continue;
            }

            if (ValidateNewEntry(entry) is { } witness)
            {
                return IngestTruthAlignmentClassification.TruthAlignmentRequired(witness);
            }
        }

        var resolvedChanges = DigestionEvaluationScopes.ResolveChanges(scope, changes);
        var authorityChangedAtomIds = DigestionStatusEvaluator.StatusAuthorityChangedAtomIds(
            planned,
            baseline,
            resolvedChanges);
        var changedCoveredEntry = planned.RequireDigestionEntries()
            .Where(static entry => !entry.CoverageGids.IsEmpty)
            .Where(entry => authorityChangedAtomIds.Contains(entry.AtomId))
            .OrderBy(static entry => entry.AtomId, StringComparer.Ordinal)
            .FirstOrDefault();
        if (changedCoveredEntry is not null)
        {
            return IngestTruthAlignmentClassification.TruthAlignmentRequired(
                $"covered entry {changedCoveredEntry.AtomId} changed status-authority inputs");
        }

        return IngestTruthAlignmentClassification.UncoveredOnly;
    }

    private static Dictionary<string, StatusAuthorityEntry> StatusAuthorityEntries(
        BackfillInventoryDocument document) =>
        document.RequireDigestionSources()
            .SelectMany(source => source.Entries.Select(entry => new StatusAuthorityEntry(source, entry)))
            .ToDictionary(static item => item.Entry.AtomId, StringComparer.Ordinal);

    private static bool StatusAuthorityEqual(StatusAuthorityEntry left, StatusAuthorityEntry right) =>
        BackfillInventoryWriter.WriteStatusAuthorityIdentity(left.Source, left.Entry)
            .AsSpan()
            .SequenceEqual(
                BackfillInventoryWriter.WriteStatusAuthorityIdentity(right.Source, right.Entry).AsSpan());

    private static string? ValidateNewEntry(DigestionLedgerEntry entry)
    {
        if (entry.CoverageGids.Length > 0)
        {
            return $"new entry {entry.AtomId} is coverage-bearing";
        }

        if (!entry.Receipts.IsEmpty)
        {
            return $"new entry {entry.AtomId} carries receipts";
        }

        return entry.ProjectedStatus != ResidualOpen
            ? $"new entry {entry.AtomId} projected status is not residual-open"
            : null;
    }

    private sealed record StatusAuthorityEntry(
        DigestionLedgerSource Source,
        DigestionLedgerEntry Entry);
}
