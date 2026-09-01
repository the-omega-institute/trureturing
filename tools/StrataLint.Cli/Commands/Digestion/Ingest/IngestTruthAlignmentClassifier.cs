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
                if (ValidateNewEntry(NormalizeNewEntryForValidation(entry)) is { } witness)
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
        DigestionLedgerAlignment alignment,
        DigestionEvaluationScope scope,
        RawChangeSet repositoryChanges)
    {
        ArgumentNullException.ThrowIfNull(current);
        ArgumentNullException.ThrowIfNull(baseline);
        ArgumentNullException.ThrowIfNull(planned);
        ArgumentNullException.ThrowIfNull(repositoryChanges);
        var currentEntries = StatusAuthorityEntries(current);
        var plannedEntries = StatusAuthorityEntries(planned);
        foreach (var item in currentEntries.Values
                     .Where(static item => !item.Entry.CoverageGids.IsEmpty)
                     .OrderBy(static item => item.Entry.AtomId, StringComparer.Ordinal))
        {
            var entry = item.Entry;
            if (!plannedEntries.TryGetValue(entry.AtomId, out var plannedItem))
            {
                return IngestTruthAlignmentClassification.TruthAlignmentRequired(
                    $"covered entry {entry.AtomId} disappeared from plan");
            }

            if (plannedItem.Entry.CoverageGids.IsEmpty)
            {
                return IngestTruthAlignmentClassification.TruthAlignmentRequired(
                    $"covered entry {entry.AtomId} coverage was cleared in plan");
            }
        }

        foreach (var item in plannedEntries.Values
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

            if (ValidateNewEntry(NormalizeNewEntryForValidation(entry)) is { } witness)
            {
                return IngestTruthAlignmentClassification.TruthAlignmentRequired(witness);
            }
        }

        var resolvedChanges = DigestionEvaluationScopes.ResolveChanges(scope, repositoryChanges);
        var authorityChangedAtomIds = DigestionStatusEvaluator.StatusAuthorityChangedAtomIds(
            planned,
            baseline,
            resolvedChanges,
            alignment);
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

    private static DigestionLedgerEntry NormalizeNewEntryForValidation(
        DigestionLedgerEntry entry) =>
        entry with
        {
            Receipts = entry.Receipts with { ChainAtoms = [] },
        };

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

        if (entry.ProjectedStatus != ResidualOpen)
        {
            return $"new entry {entry.AtomId} projected status is not residual-open";
        }

        return null;
    }

    private sealed record StatusAuthorityEntry(
        DigestionLedgerSource Source,
        DigestionLedgerEntry Entry);
}
