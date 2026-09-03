using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed partial class BackfillInventoryDocument
{
    private static Dictionary<string, object?> ProjectLegacyCoverage(
        Dictionary<string, object?> entry,
        string sourceId)
    {
        ExactKeys(entry, EntryFieldUniverse, $"source {sourceId} entry");
        var atomId = Scalar(entry, "atom_id", $"source {sourceId} atom_id");
        var rawCoverage = List(
            entry,
            "coverage_gids",
            $"entry {atomId} coverage_gids must be a list");
        var containsLegacyGid = rawCoverage.Any(static item => item is string);
        var containsCurrentEdge = rawCoverage.Any(static item => item is Dictionary<string, object?>);
        if (containsLegacyGid && containsCurrentEdge)
        {
            throw new FormatException(
                $"entry {atomId} coverage_gids cannot mix legacy scalars and current edges");
        }

        var receipts = Mapping(
            entry.GetValueOrDefault("receipts"),
            $"entry {atomId} receipts must be a mapping");
        var hasLegacyCoverageReceipts = receipts.ContainsKey("coverage");
        var hasLegacyRecordedAt = receipts.GetValueOrDefault("cover_disposition")
            is Dictionary<string, object?> rawLegacyDisposition
            && rawLegacyDisposition.ContainsKey("recorded_at_utc");
        if (!containsLegacyGid
            && (containsCurrentEdge || (!hasLegacyCoverageReceipts && !hasLegacyRecordedAt)))
        {
            return entry;
        }

        var legacyGids = Strings(rawCoverage, $"entry {atomId} coverage_gids");
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

        return new Dictionary<string, object?>(entry, StringComparer.Ordinal)
        {
            ["coverage_gids"] = coverage,
            ["receipts"] = projectedReceipts,
        };
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
