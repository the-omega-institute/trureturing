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

    internal static DigestionReadinessRecord ClassifyEntry(
        DigestionFrontierEntry frontier) => frontier.PrimaryDisposition switch
    {
        DigestionFrontierDisposition.Quarantined => Record(
                frontier.Entry,
                "quarantined",
                ["quarantine:" + frontier.PrimaryDetail]),
        DigestionFrontierDisposition.Withheld =>
            frontier.PrimaryDetail == "acknowledged-stale"
                ? Record(frontier.Entry, "refresh-stale", [frontier.PrimaryDetail])
                : Record(frontier.Entry, "withheld", [frontier.PrimaryDetail]),
        DigestionFrontierDisposition.ChainChild =>
            Record(frontier.Entry, "chain-child", frontier.ParentAtomIds),
        DigestionFrontierDisposition.NotFormalizable => Record(
                frontier.Entry,
                "not-formalizable",
                ["non-assertion-ast-kind:" + frontier.KindLabel]),
        DigestionFrontierDisposition.FormalizableClaim => ClassifyFormalizable(frontier),
        _ => throw DigestionFrontierDispositionPolicy.Unsupported(frontier.PrimaryDisposition),
    };

    private static DigestionReadinessRecord ClassifyFormalizable(
        DigestionFrontierEntry frontier)
    {
        var entry = frontier.Entry;
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
