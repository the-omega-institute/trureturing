using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed partial class BackfillInventoryDocument
{
    private static DigestionReceipts ParseReceipts(
        string atomId,
        object? rawReceipts,
        bool allowLegacyCoverageReceipts)
    {
        var receipts = Mapping(rawReceipts, $"entry {atomId} receipts must be a mapping");

        // The optional live receipt fields remain strict whenever they are present.
        ExactKeys(
            receipts,
            ["coverage", "scribe", "unresolved_subitems"],
            ["chain_atoms", "tail_authorization", "quarantine", "cover_disposition"],
            $"entry {atomId} receipts");
        var coverage = ImmutableArray.CreateBuilder<DigestionCoverageReceipt>();
        foreach (var rawCoverage in List(receipts, "coverage", $"entry {atomId} coverage receipts must be a list"))
        {
            var item = Mapping(rawCoverage, $"entry {atomId} coverage receipt must be a mapping");
            var itemKeys = item.Keys.ToHashSet(StringComparer.Ordinal);
            var currentKeys = new[] { "gid", "source_sha256", "target_statement_id" };
            var legacyKeys = new[] { "gid", "source_sha256", "target_sha256" };
            var isCurrent = itemKeys.SetEquals(currentKeys);
            var isLegacy = allowLegacyCoverageReceipts && itemKeys.SetEquals(legacyKeys);
            if (!isCurrent && !isLegacy)
            {
                throw new FormatException(
                    $"entry {atomId} coverage receipt keys are not canonical");
            }

            var gid = Scalar(item, "gid", $"entry {atomId} coverage gid");
            var sourceSha256 = Scalar(
                item,
                "source_sha256",
                $"entry {atomId} coverage source_sha256");
            coverage.Add(isLegacy
                ? DigestionCoverageReceipt.FromLegacyTargetSha256(
                    gid,
                    sourceSha256,
                    Scalar(
                        item,
                        "target_sha256",
                        $"entry {atomId} coverage legacy target_sha256"))
                : new DigestionCoverageReceipt(
                    gid,
                    sourceSha256,
                    Scalar(
                        item,
                        "target_statement_id",
                        $"entry {atomId} coverage target_statement_id")));
        }

        var scribe = ImmutableArray.CreateBuilder<DigestionScribeReceipt>();
        foreach (var rawScribe in List(receipts, "scribe", $"entry {atomId} scribe receipts must be a list"))
        {
            var item = Mapping(rawScribe, $"entry {atomId} scribe receipt must be a mapping");
            ExactKeys(item, ["gid", "definition_sha256", "emission_sha256"], $"entry {atomId} scribe receipt");
            scribe.Add(new DigestionScribeReceipt(
                Scalar(item, "gid", $"entry {atomId} scribe gid"),
                Scalar(item, "definition_sha256", $"entry {atomId} definition_sha256"),
                Scalar(item, "emission_sha256", $"entry {atomId} emission_sha256")));
        }

        DigestionExternalReceipt? tailAuthorization = null;
        if (receipts.GetValueOrDefault("tail_authorization") is { } rawTail)
        {
            var tail = Mapping(rawTail, $"entry {atomId} tail_authorization must be null or a mapping");
            ExactKeys(tail, ["path", "sha256"], $"entry {atomId} tail_authorization");
            tailAuthorization = new DigestionExternalReceipt(
                Scalar(tail, "path", $"entry {atomId} tail authorization path"),
                Scalar(tail, "sha256", $"entry {atomId} tail authorization sha256"));
        }

        DigestionQuarantine? quarantine = null;
        if (receipts.ContainsKey("quarantine"))
        {
            var rawQuarantine = Mapping(
                receipts.GetValueOrDefault("quarantine"),
                $"entry {atomId} quarantine must be a mapping");
            if (!rawQuarantine.ContainsKey("justification"))
            {
                throw new FormatException(
                    $"entry {atomId} quarantine justification is required");
            }

            if (!rawQuarantine.ContainsKey("reentry_condition"))
            {
                throw new FormatException(
                    $"entry {atomId} quarantine reentry_condition is required");
            }

            ExactKeys(
                rawQuarantine,
                rawQuarantine.ContainsKey("blocker_class")
                    ? ["justification", "reentry_condition", "blocker_class"]
                    : ["justification", "reentry_condition"],
                $"entry {atomId} quarantine");
            string? blockerClass = null;
            if (rawQuarantine.ContainsKey("blocker_class"))
            {
                blockerClass = Scalar(
                    rawQuarantine,
                    "blocker_class",
                    $"entry {atomId} quarantine blocker_class");
                if (!DigestionQuarantine.BlockerClasses.Contains(blockerClass, StringComparer.Ordinal))
                {
                    throw new FormatException(
                        $"entry {atomId} quarantine blocker_class '{blockerClass}' is not one of "
                        + string.Join(", ", DigestionQuarantine.BlockerClasses));
                }
            }

            quarantine = new DigestionQuarantine(
                Scalar(rawQuarantine, "justification", $"entry {atomId} quarantine justification"),
                Scalar(rawQuarantine, "reentry_condition", $"entry {atomId} quarantine reentry_condition"),
                blockerClass);
        }

        return new DigestionReceipts(
            coverage.ToImmutable(),
            scribe.ToImmutable(),
            Strings(
                List(receipts, "unresolved_subitems", $"entry {atomId} unresolved_subitems must be a list"),
                $"entry {atomId} unresolved_subitems"),
            receipts.ContainsKey("chain_atoms")
                ? Strings(
                    List(receipts, "chain_atoms", $"entry {atomId} chain_atoms must be a list"),
                    $"entry {atomId} chain_atoms")
                : [],
            tailAuthorization,
            quarantine,
            ParseCoverDisposition(atomId, receipts));
    }
}
