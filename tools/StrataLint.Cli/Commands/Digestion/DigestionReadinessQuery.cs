using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record DigestionReadinessRecord(
    string SourceId,
    string AtomId,
    ImmutableArray<string> CoverageGids,
    string Action,
    ImmutableArray<string> OrderedBlockers,
    ImmutableArray<string> UnknownPredicates);

internal static class DigestionReadinessQuery
{
    private static readonly ImmutableDictionary<string, int> ActionPriorities =
        new Dictionary<string, int>(StringComparer.Ordinal)
        {
            ["quarantined"] = 0,
            ["withheld"] = 1,
            ["refresh-stale"] = 2,
            ["not-formalizable"] = 3,
            ["chain-child"] = 4,
            ["close-chain"] = 5,
            ["deposit"] = 6,
        }.ToImmutableDictionary(StringComparer.Ordinal);

    internal static ImmutableArray<DigestionReadinessRecord> Classify(
        DigestionFrontierProjection projection)
    {
        ArgumentNullException.ThrowIfNull(projection);

        return projection.Entries
            .Select(ClassifyEntry)
            .OrderBy(static item => ActionPriorities[item.Action])
            .ThenBy(static item => item.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.AtomId, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static DigestionReadinessRecord ClassifyEntry(
        DigestionFrontierEntry frontier)
    {
        var entry = frontier.Entry;
        if (frontier.PrimaryDisposition == DigestionFrontierDisposition.Quarantined)
        {
            return Record(
                entry,
                "quarantined",
                frontier.PrimaryDetail == "untyped"
                    ? ["quarantine"]
                    : ["quarantine:" + frontier.PrimaryDetail]);
        }

        if (frontier.PrimaryDisposition == DigestionFrontierDisposition.Withheld)
        {
            return frontier.PrimaryDetail == "acknowledged-stale"
                ? Record(entry, "refresh-stale", [frontier.PrimaryDetail])
                : Record(entry, "withheld", [frontier.PrimaryDetail]);
        }

        if (frontier.PrimaryDisposition == DigestionFrontierDisposition.ChainChild)
        {
            return Record(entry, "chain-child", frontier.ParentAtomIds);
        }

        if (frontier.PrimaryDisposition == DigestionFrontierDisposition.NotFormalizable)
        {
            return Record(
                entry,
                "not-formalizable",
                ["non-assertion-ast-kind:" + frontier.KindLabel]);
        }

        var openChildren = entry.Receipts.ChainAtoms
            .Where(atomId => frontier.Evaluation.Gaps.Any(gap =>
                string.Equals(gap.Code, "chain-migration-incomplete", StringComparison.Ordinal)
                && string.Equals(gap.Detail, atomId, StringComparison.Ordinal)))
            .ToImmutableArray();
        if (!openChildren.IsEmpty)
        {
            return Record(entry, "close-chain", openChildren);
        }

        return Record(entry, "deposit", []);
    }

    private static DigestionReadinessRecord Record(
        DigestionLedgerEntry entry,
        string action,
        ImmutableArray<string> orderedBlockers,
        ImmutableArray<string> unknownPredicates = default) => new(
            entry.SourceId,
            entry.AtomId,
            entry.CoverageGids,
            action,
            orderedBlockers,
            unknownPredicates.IsDefault ? [] : unknownPredicates);
}
