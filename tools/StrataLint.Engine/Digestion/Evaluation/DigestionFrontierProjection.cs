using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum DigestionFrontierDisposition
{
    Quarantined,
    Withheld,
    ChainChild,
    NotFormalizable,
    FormalizableClaim,
}

internal static class DigestionFrontierDispositionPolicy
{
    internal static InvalidOperationException Unsupported(
        DigestionFrontierDisposition disposition) =>
        new($"unsupported disposition {disposition}");
}

internal sealed record DigestionFrontierEntry(
    DigestionEntryEvaluation Evaluation,
    DigestionFrontierDisposition PrimaryDisposition,
    string PrimaryDetail,
    DigestionContentRole ContentRole,
    string KindLabel,
    string? StatusQualifier,
    bool IsChainChild,
    ImmutableArray<string> ParentAtomIds,
    bool HasCoverDisposition,
    bool IsAcknowledgedStale)
{
    internal DigestionLedgerEntry Entry => Evaluation.Entry;

    internal string PrimaryDispositionLabel => PrimaryDisposition switch
    {
        DigestionFrontierDisposition.Quarantined => "quarantined",
        DigestionFrontierDisposition.Withheld => "withheld",
        DigestionFrontierDisposition.ChainChild => "chain-child",
        DigestionFrontierDisposition.NotFormalizable => "not-formalizable",
        DigestionFrontierDisposition.FormalizableClaim => "formalizable-claim",
        _ => throw DigestionFrontierDispositionPolicy.Unsupported(PrimaryDisposition),
    };
}

internal sealed record DigestionFrontierCounts(
    int Quarantined,
    int Withheld,
    int ChainChild,
    int NotFormalizable,
    int FormalizableClaim)
{
    internal int ResidualOpen =>
        Quarantined + Withheld + ChainChild + NotFormalizable + FormalizableClaim;

    internal int FormalizationFrontier => FormalizableClaim;

    internal static DigestionFrontierCounts From(IEnumerable<DigestionFrontierEntry> entries)
    {
        var counts = (Quarantined: 0, Withheld: 0, ChainChild: 0, NotFormalizable: 0, FormalizableClaim: 0);
        foreach (var entry in entries)
        {
            counts = entry.PrimaryDisposition switch
            {
                DigestionFrontierDisposition.Quarantined => counts with
                {
                    Quarantined = counts.Quarantined + 1,
                },
                DigestionFrontierDisposition.Withheld => counts with
                {
                    Withheld = counts.Withheld + 1,
                },
                DigestionFrontierDisposition.ChainChild => counts with
                {
                    ChainChild = counts.ChainChild + 1,
                },
                DigestionFrontierDisposition.NotFormalizable => counts with
                {
                    NotFormalizable = counts.NotFormalizable + 1,
                },
                DigestionFrontierDisposition.FormalizableClaim => counts with
                {
                    FormalizableClaim = counts.FormalizableClaim + 1,
                },
                _ => throw DigestionFrontierDispositionPolicy.Unsupported(entry.PrimaryDisposition),
            };
        }

        return new DigestionFrontierCounts(
            counts.Quarantined,
            counts.Withheld,
            counts.ChainChild,
            counts.NotFormalizable,
            counts.FormalizableClaim);
    }
}

internal sealed record DigestionFrontierSourceCounts(
    string SourceId,
    DigestionFrontierCounts Counts);

internal sealed class DigestionFrontierProjection
{
    private DigestionFrontierProjection(
        ImmutableArray<DigestionFrontierEntry> entries,
        ImmutableArray<DigestionFrontierSourceCounts> perSource)
    {
        Entries = entries;
        PerSource = perSource;
        Total = DigestionFrontierCounts.From(entries);
        FormalizationFrontier = entries
            .Where(static entry => IsFormalizationFrontierDisposition(
                entry.PrimaryDisposition))
            .ToImmutableArray();
    }

    internal ImmutableArray<DigestionFrontierEntry> Entries { get; }
    internal ImmutableArray<DigestionFrontierEntry> FormalizationFrontier { get; }
    internal ImmutableArray<DigestionFrontierSourceCounts> PerSource { get; }
    internal DigestionFrontierCounts Total { get; }

    internal static bool IsFormalizationFrontierDisposition(
        DigestionFrontierDisposition disposition) => disposition switch
    {
        DigestionFrontierDisposition.Quarantined => false,
        DigestionFrontierDisposition.Withheld => false,
        DigestionFrontierDisposition.ChainChild => false,
        DigestionFrontierDisposition.NotFormalizable => false,
        DigestionFrontierDisposition.FormalizableClaim => true,
        _ => throw DigestionFrontierDispositionPolicy.Unsupported(disposition),
    };

    internal static DigestionFrontierProjection Create(
        BackfillInventoryDocument ledger,
        DigestionLedgerEvaluation evaluation,
        IReadOnlyDictionary<string, string> contentKinds,
        bool retryDispositions)
    {
        ArgumentNullException.ThrowIfNull(ledger);
        ArgumentNullException.ThrowIfNull(evaluation);
        ArgumentNullException.ThrowIfNull(contentKinds);

        var staleAtomIds = ledger.RequireDigestionSources()
            .SelectMany(static source => source.AcknowledgedStale)
            .ToImmutableHashSet(StringComparer.Ordinal);
        var parentsByChild = BuildParentsByChild(ledger.RequireDigestionEntries());
        var entries = evaluation.Entries
            .Where(static item =>
                item.DerivedStatus.Migration == DigestionMigrationState.Residual
                && item.DerivedStatus.Truth == DigestionTruthState.Open)
            .Select(item => ProjectEntry(
                item,
                contentKinds,
                staleAtomIds,
                parentsByChild,
                retryDispositions))
            .OrderBy(static item => item.Entry.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item.Entry.AtomId, StringComparer.Ordinal)
            .ToImmutableArray();
        var perSource = ledger.RequireDigestionSources()
            .Select(source => new DigestionFrontierSourceCounts(
                source.SourceId,
                DigestionFrontierCounts.From(entries.Where(entry =>
                    string.Equals(entry.Entry.SourceId, source.SourceId, StringComparison.Ordinal)))))
            .OrderBy(static source => source.SourceId, StringComparer.Ordinal)
            .ToImmutableArray();
        return new DigestionFrontierProjection(entries, perSource);
    }

    private static ImmutableDictionary<string, ImmutableArray<string>> BuildParentsByChild(
        IEnumerable<DigestionLedgerEntry> entries)
    {
        var parents = new Dictionary<string, SortedSet<string>>(StringComparer.Ordinal);
        foreach (var parent in entries)
        {
            foreach (var childAtomId in parent.Receipts.ChainAtoms)
            {
                if (!parents.TryGetValue(childAtomId, out var parentIds))
                {
                    parentIds = new SortedSet<string>(StringComparer.Ordinal);
                    parents.Add(childAtomId, parentIds);
                }

                parentIds.Add(parent.AtomId);
            }
        }

        return parents.ToImmutableDictionary(
            static pair => pair.Key,
            static pair => pair.Value.ToImmutableArray(),
            StringComparer.Ordinal);
    }

    private static DigestionFrontierEntry ProjectEntry(
        DigestionEntryEvaluation evaluation,
        IReadOnlyDictionary<string, string> contentKinds,
        IReadOnlySet<string> staleAtomIds,
        IReadOnlyDictionary<string, ImmutableArray<string>> parentsByChild,
        bool retryDispositions)
    {
        var entry = evaluation.Entry;
        contentKinds.TryGetValue(entry.AtomId, out var contentKind);
        var content = DigestionContentDisposition.Resolve(contentKind);
        var parentIds = parentsByChild.GetValueOrDefault(entry.AtomId, []);
        var isChainChild = !parentIds.IsEmpty;
        var hasCoverDisposition = entry.Receipts.CoverDisposition is not null;
        var withholdCoverDisposition = DigestionCoverDispositionSelector.Classify(
            entry,
            retryDispositions) == DigestionCoverDispositionSelection.Withheld;
        var isAcknowledgedStale = staleAtomIds.Contains(entry.AtomId);
        DigestionFrontierDisposition disposition;
        string detail;
        string? statusQualifier = null;
        if (entry.Receipts.Quarantine is { } quarantine)
        {
            disposition = DigestionFrontierDisposition.Quarantined;
            detail = quarantine.BlockerClass;
        }
        else
        {
            var status = evaluation.Atom?.StatusMarker;
            var withholding = withholdCoverDisposition
                ? (Reason: DigestionCoverDispositionSelector.WithholdReason, Qualifier: (string?)null)
                : isAcknowledgedStale
                    ? (Reason: "acknowledged-stale", Qualifier: (string?)null)
                    : status?.Kind == DigestionAtomStatusMarkerKind.Malformed
                        ? (Reason: "malformed-status-marker", Qualifier: status.Qualifier)
                    : status is
                        {
                            Kind: DigestionAtomStatusMarkerKind.Valid,
                            Status: "closed",
                            Qualifier.Length: > 0,
                        }
                            ? (Reason: "qualified-closed-status", Qualifier: status.Qualifier)
                            : (Reason: (string?)null, Qualifier: (string?)null);
            if (withholding.Reason is not null)
            {
                disposition = DigestionFrontierDisposition.Withheld;
                detail = withholding.Reason;
                statusQualifier = withholding.Qualifier;
            }
            else if (isChainChild)
            {
                disposition = DigestionFrontierDisposition.ChainChild;
                detail = "chain-child";
            }
            else if (content.Role == DigestionContentRole.NotFormalizable)
            {
                disposition = DigestionFrontierDisposition.NotFormalizable;
                detail = content.KindLabel;
            }
            else if (status is null)
            {
                throw new FormatException($"entry {entry.AtomId} has no canonical atom alignment");
            }
            else
            {
                disposition = DigestionFrontierDisposition.FormalizableClaim;
                detail = "formalizable-claim";
            }
        }

        return new DigestionFrontierEntry(
            evaluation,
            disposition,
            detail,
            content.Role,
            content.KindLabel,
            statusQualifier,
            isChainChild,
            parentIds,
            hasCoverDisposition,
            isAcknowledgedStale);
    }
}
