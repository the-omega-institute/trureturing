using System.Collections.Immutable;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal sealed record DigestionReadinessRecord(
    string SourceId,
    string AtomId,
    string Action,
    ImmutableArray<string> OrderedBlockers,
    ImmutableArray<string> UnknownPredicates);

internal static class DigestionReadinessQuery
{
    private static readonly ImmutableArray<string> CoverUnknownPredicates =
    [
        "cover-atom:frozen-statement-resolution",
        "cover-atom:baseline-precommitment-ownership",
    ];

    private static readonly ImmutableDictionary<string, int> ActionPriorities =
        new Dictionary<string, int>(StringComparer.Ordinal)
        {
            ["quarantined"] = 0,
            ["withheld"] = 1,
            ["refresh-stale"] = 2,
            ["not-formalizable"] = 3,
            ["needs-routing"] = 4,
            ["close-chain"] = 5,
            ["cover-now"] = 6,
            ["repair-scribe"] = 7,
            ["deposit"] = 8,
        }.ToImmutableDictionary(StringComparer.Ordinal);

    internal static ImmutableArray<DigestionReadinessRecord> Classify(
        BackfillInventoryDocument ledger,
        DigestionLedgerEvaluation evaluation,
        IReadOnlyDictionary<string, string> contentKinds,
        IReadOnlyDictionary<string, DigestionFormalizationReceipt> currentReceipts,
        IReadOnlySet<string> presentReceiptAtomIds,
        VerifiedScribeEmissions scribeEmissions)
    {
        ArgumentNullException.ThrowIfNull(ledger);
        ArgumentNullException.ThrowIfNull(evaluation);
        ArgumentNullException.ThrowIfNull(contentKinds);
        ArgumentNullException.ThrowIfNull(currentReceipts);
        ArgumentNullException.ThrowIfNull(presentReceiptAtomIds);
        ArgumentNullException.ThrowIfNull(scribeEmissions);

        var staleAtomIds = ledger.RequireDigestionSources()
            .SelectMany(static source => source.AcknowledgedStale)
            .ToImmutableHashSet(StringComparer.Ordinal);
        return evaluation.Entries
            .Where(static item =>
                item.DerivedStatus.Migration == DigestionMigrationState.Residual
                && item.DerivedStatus.Truth == DigestionTruthState.Open)
            .Select(item => ClassifyEntry(
                item,
                staleAtomIds,
                contentKinds,
                currentReceipts,
                presentReceiptAtomIds,
                scribeEmissions))
            .OrderBy(static item => ActionPriorities[item.Action])
            .ThenBy(static item => item.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.AtomId, StringComparer.Ordinal)
            .ToImmutableArray();
    }

    private static DigestionReadinessRecord ClassifyEntry(
        DigestionEntryEvaluation evaluation,
        IReadOnlySet<string> staleAtomIds,
        IReadOnlyDictionary<string, string> contentKinds,
        IReadOnlyDictionary<string, DigestionFormalizationReceipt> currentReceipts,
        IReadOnlySet<string> presentReceiptAtomIds,
        VerifiedScribeEmissions scribeEmissions)
    {
        var entry = evaluation.Entry;
        if (entry.Receipts.Quarantine is { } quarantine)
        {
            return Record(
                entry,
                "quarantined",
                quarantine.BlockerClass is null
                    ? ["quarantine"]
                    : ["quarantine:" + quarantine.BlockerClass]);
        }

        if (DigestionCoverDispositionSelector.Classify(entry, retryDispositions: false)
            == DigestionCoverDispositionSelection.Withheld)
        {
            return Record(entry, "withheld", [DigestionCoverDispositionSelector.WithholdReason]);
        }

        if (staleAtomIds.Contains(entry.AtomId))
        {
            return Record(entry, "refresh-stale", ["acknowledged-stale"]);
        }

        if (contentKinds.TryGetValue(entry.AtomId, out var contentKind)
            && DigestionContentKindPolicy.IsNotFormalizable(contentKind))
        {
            return Record(
                entry,
                "not-formalizable",
                ["non-assertion-ast-kind:" + contentKind]);
        }

        if (contentKind is null || !DigestionContentKindPolicy.IsFormalizable(contentKind))
        {
            return Record(entry, "needs-routing", ["unsupported-ast-kind"]);
        }

        var openChildren = entry.Receipts.ChainAtoms
            .Where(atomId => evaluation.Gaps.Any(gap =>
                string.Equals(gap.Code, "chain-migration-incomplete", StringComparison.Ordinal)
                && string.Equals(gap.Detail, atomId, StringComparison.Ordinal)))
            .ToImmutableArray();
        if (!openChildren.IsEmpty)
        {
            return Record(entry, "close-chain", openChildren);
        }

        if (!currentReceipts.TryGetValue(entry.AtomId, out var receipt))
        {
            return Record(
                entry,
                "deposit",
                presentReceiptAtomIds.Contains(entry.AtomId)
                    ? ["formalization-receipt-stale"]
                    : ["formalization-receipt-missing"]);
        }

        var blockers = ImmutableArray.CreateBuilder<string>();
        var unknownPredicates = ImmutableArray.CreateBuilder<string>();
        foreach (var gidText in receipt.RegisteredGids)
        {
            if (!Gid.TryParse(gidText, out var gid)
                || gid.ToTarget() is not Target.Formal { Declaration: not null })
            {
                blockers.Add("scribe-readiness-unknown:" + gidText);
                unknownPredicates.Add("scribe-readiness:formalization-gid-not-declaration");
                continue;
            }

            var documentGid = ScribeEmissionAttestation.DocumentGid(gidText);
            if (!scribeEmissions.TryGet(documentGid, out _))
            {
                blockers.Add("scribe-emission-missing:" + gidText);
                continue;
            }

            if (!scribeEmissions.ReferencesDeclaration(gidText))
            {
                blockers.Add("scribe-declaration-reference-missing:" + gidText);
            }
        }

        return blockers.Count == 0
            ? Record(entry, "cover-now", [], CoverUnknownPredicates)
            : Record(entry, "repair-scribe", blockers.ToImmutable(), unknownPredicates.ToImmutable());
    }

    private static DigestionReadinessRecord Record(
        DigestionLedgerEntry entry,
        string action,
        ImmutableArray<string> orderedBlockers,
        ImmutableArray<string> unknownPredicates = default) => new(
            entry.SourceId,
            entry.AtomId,
            action,
            orderedBlockers,
            unknownPredicates.IsDefault ? [] : unknownPredicates);
}
