using System.Collections.Immutable;

namespace StrataLint.Engine;

internal static partial class BackfillInventoryLoader
{
    internal static BackfillInventoryDocument LoadStatementIdHistoryBaseline(
        RepositorySnapshot snapshot) =>
        LoadSnapshot(snapshot, LoadStatementIdHistoryBaselineDirectorySnapshot);

    private static BackfillInventoryDocument LoadStatementIdHistoryBaselineDirectorySnapshot(
        RepositorySnapshot snapshot) =>
        LoadDirectorySnapshot(
            snapshot,
            ParseBaselineSourceMetadata,
            projectBaselineCoverage: false,
            allowUnknownEntryFields: true);

    private static ImmutableArray<DigestionLedgerSource> ProjectBaselineReferences(
        ImmutableArray<DigestionLedgerSource> sources,
        IReadOnlyDictionary<string, string> atomIds) =>
        sources.Select(source => source with
        {
            AcknowledgedStale = ProjectAtomIds(source.AcknowledgedStale, atomIds),
            Entries = source.Entries.Select(entry => entry with
            {
                Receipts = entry.Receipts with
                {
                    ChainAtoms = ProjectAtomIds(entry.Receipts.ChainAtoms, atomIds),
                },
            }).ToImmutableArray(),
        }).ToImmutableArray();

    private static ImmutableArray<string> ProjectAtomIds(
        ImmutableArray<string> values,
        IReadOnlyDictionary<string, string> atomIds) =>
        values.Select(value => atomIds.GetValueOrDefault(value, value)).ToImmutableArray();
}
