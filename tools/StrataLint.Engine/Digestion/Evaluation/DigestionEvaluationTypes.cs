using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal enum DigestionGapSeverity
{
    NonFatal,
    ReceiptIntegrityFailure,
}

internal sealed record DigestionGap(
    string Code,
    string Detail,
    DigestionGapSeverity Severity);

internal readonly record struct DigestionReceiptIntegrityGapIdentity(
    string AtomId,
    string Code,
    string Detail);

internal static class DigestionReceiptIntegrity
{
    internal static ImmutableArray<DigestionReceiptIntegrityGapIdentity> Identities(
        DigestionLedgerEvaluation evaluation) =>
        evaluation.ReceiptIntegrityGaps
            .Select(static item => new DigestionReceiptIntegrityGapIdentity(
                item.Entry.AtomId,
                item.Gap.Code,
                item.Gap.Detail))
            .Distinct()
            .OrderBy(static identity => identity.AtomId, StringComparer.Ordinal)
            .ThenBy(static identity => identity.Code, StringComparer.Ordinal)
            .ThenBy(static identity => identity.Detail, StringComparer.Ordinal)
            .ToImmutableArray();

    internal static ImmutableArray<DigestionReceiptIntegrityGapIdentity> NewFailureIdentities(
        IEnumerable<DigestionReceiptIntegrityGapIdentity> forkPoint,
        DigestionLedgerEvaluation candidate)
    {
        ArgumentNullException.ThrowIfNull(forkPoint);
        var baseline = forkPoint.ToHashSet();
        return Identities(candidate)
            .Where(identity => !baseline.Contains(identity))
            .ToImmutableArray();
    }

    internal static string Render(DigestionReceiptIntegrityGapIdentity identity) =>
        $"{identity.AtomId}:{identity.Code}:{identity.Detail}";
}

internal sealed record DigestionEntryEvaluation(
    DigestionLedgerEntry Entry,
    DigestionReceiptAlignment Alignment,
    DigestionAtom? Atom,
    DigestionStatus DerivedStatus,
    bool Deletable,
    ImmutableArray<DigestionGap> Gaps)
{
    internal DigestionEntryEvaluation(
        DigestionLedgerEntry entry,
        DigestionReceiptAlignment alignment,
        DigestionStatus derivedStatus,
        bool deletable,
        ImmutableArray<DigestionGap> gaps)
        : this(entry, alignment, null, derivedStatus, deletable, gaps)
    {
    }

    internal string Render() =>
        $"{Entry.SourceId}/{Entry.AtomId} "
        + $"alignment={DigestionReceiptAlignmentNames.Render(Alignment)} "
        + $"{DigestionStatusNames.Migration(DerivedStatus.Migration)}-"
        + $"{DigestionStatusNames.Truth(DerivedStatus.Truth)} "
        + $"deletable={Deletable.ToString().ToLowerInvariant()} "
        + $"gaps={string.Join(',', Gaps.Select(static gap => gap.Code))}";
}

internal sealed record DigestionLedgerEvaluation(
    ImmutableArray<DigestionEntryEvaluation> Entries,
    ImmutableArray<string> Findings,
    // 非阻断的观察项:「已入库、尚未消化」。与 Findings 分开承载,使效力由**类型**
    // 决定而非由消费者按字符串猜(CLAUDE.md:好原材料无法被误读)。
    ImmutableArray<string> ObservationalFindings = default)
{
    internal ImmutableArray<string> Observations =>
        ObservationalFindings.IsDefault ? [] : ObservationalFindings;

    internal int DeletableCount => Entries.Count(static entry => entry.Deletable);

    internal IEnumerable<(DigestionLedgerEntry Entry, DigestionGap Gap)> ReceiptIntegrityGaps =>
        Entries.SelectMany(static entry => entry.Gaps
            .Where(static gap => gap.Severity == DigestionGapSeverity.ReceiptIntegrityFailure)
            .Select(gap => (entry.Entry, gap)));

    internal IEnumerable<string> ReceiptIntegrityFailureReasons =>
        Findings.Concat(ReceiptIntegrityGaps.Select(static item =>
            $"{item.Entry.AtomId}:{item.Gap.Code}:{item.Gap.Detail}"));

    internal bool HasReceiptIntegrityFailure =>
        Findings.Length > 0
        || ReceiptIntegrityGaps.Any();
}

internal static class DigestionStatusNames
{
    internal static string Migration(DigestionMigrationState value) => value switch
    {
        DigestionMigrationState.Residual => "residual",
        DigestionMigrationState.Partial => "partial",
        DigestionMigrationState.Absorbed => "absorbed",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    internal static string Truth(DigestionTruthState value) => value switch
    {
        DigestionTruthState.Closed => "closed",
        DigestionTruthState.Tail => "tail",
        DigestionTruthState.Open => "open",
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };
}
