using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed partial class BackfillInventoryDocument
{
    private static readonly string[] LegacyEntryFields =
    [
        "atom_id",
        "fingerprints",
        "cas_ref",
        "coverage_gids",
        "receipts",
        "status",
    ];

    private static Dictionary<string, object?> ProjectLegacyBaselineCoverage(
        Dictionary<string, object?> entry,
        string sourceId)
    {
        if (entry.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(
                BackfillInventoryDocument.EntryFieldUniverse))
        {
            return entry;
        }

        if (!entry.Keys.ToHashSet(StringComparer.Ordinal).SetEquals(LegacyEntryFields))
        {
            var schema = entry.ContainsKey("coverage") ? "entry" : "legacy entry";
            throw new FormatException($"source {sourceId} {schema} keys are not canonical");
        }

        // expand phase of the L2 coverage-edge migration (#5018); contract in L2b: delete once dev's base is canonical
        var atomId = Scalar(entry, "atom_id", $"source {sourceId} atom_id");
        var legacyGids = Strings(
            List(entry, "coverage_gids", $"entry {atomId} coverage_gids must be a list"),
            $"entry {atomId} coverage_gids");
        var receipts = Mapping(
            entry.GetValueOrDefault("receipts"),
            $"entry {atomId} receipts must be a mapping");
        ExactKeys(
            receipts,
            ["scribe", "unresolved_subitems"],
            ["coverage", "chain_atoms", "tail_authorization", "quarantine", "cover_disposition"],
            $"entry {atomId} receipts");

        var receiptTargets = new Dictionary<string, string?>(StringComparer.Ordinal);
        if (receipts.ContainsKey("coverage"))
        {
            foreach (var rawReceipt in List(
                         receipts,
                         "coverage",
                         $"entry {atomId} coverage receipts must be a list"))
            {
                var receipt = Mapping(
                    rawReceipt,
                    $"entry {atomId} coverage receipt must be a mapping");
                ExactKeys(
                    receipt,
                    ["gid", "source_sha256", "target_statement_id"],
                    ["statement_id_history"],
                    $"entry {atomId} coverage receipt");
                var gid = Scalar(receipt, "gid", $"entry {atomId} coverage gid");
                _ = Scalar(
                    receipt,
                    "source_sha256",
                    $"entry {atomId} coverage source_sha256");
                var target = NullableScalar(
                    receipt,
                    "target_statement_id",
                    $"entry {atomId} coverage target_statement_id");
                if (receipt.ContainsKey("statement_id_history"))
                {
                    _ = List(
                        receipt,
                        "statement_id_history",
                        $"entry {atomId} statement_id_history must be a list");
                }

                if (!receiptTargets.TryAdd(gid, target))
                {
                    throw new FormatException(
                        $"entry {atomId} has duplicate coverage receipt GID {gid}");
                }
            }
        }

        var coverage = legacyGids
            .Concat(receiptTargets.Keys)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .Select(gid => (object?)new Dictionary<string, object?>(StringComparer.Ordinal)
            {
                ["gid"] = gid,
                ["target_statement_id"] = receiptTargets.GetValueOrDefault(gid),
            })
            .ToList();
        var projectedReceipts = new Dictionary<string, object?>(receipts, StringComparer.Ordinal);
        projectedReceipts.Remove("coverage");
        if (projectedReceipts.GetValueOrDefault("cover_disposition") is { } rawDisposition)
        {
            var disposition = Mapping(
                rawDisposition,
                $"entry {atomId} cover_disposition must be a mapping");
            ExactKeys(
                disposition,
                ["outcome", "gids", "gaps"],
                ["recorded_at_utc"],
                $"entry {atomId} cover_disposition");
            if (disposition.ContainsKey("recorded_at_utc"))
            {
                _ = Scalar(
                    disposition,
                    "recorded_at_utc",
                    $"entry {atomId} cover_disposition recorded_at_utc");
                var projectedDisposition = new Dictionary<string, object?>(
                    disposition,
                    StringComparer.Ordinal);
                projectedDisposition.Remove("recorded_at_utc");
                projectedReceipts["cover_disposition"] = projectedDisposition;
            }
        }

        var projectedEntry = new Dictionary<string, object?>(entry, StringComparer.Ordinal)
        {
            ["coverage"] = coverage,
            ["receipts"] = projectedReceipts,
        };
        projectedEntry.Remove("coverage_gids");
        return projectedEntry;
    }
}

internal static partial class BackfillInventoryLoader
{
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
