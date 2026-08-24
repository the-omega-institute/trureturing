using System.Collections.Immutable;
using System.Text;

namespace StrataLint.Engine;

internal enum DigestionGapSeverity
{
    NonFatal,
    ReceiptIntegrityFailure,
}

internal sealed record DigestionGap
{
    internal DigestionGap(string code, string detail)
    {
        Code = code;
        Detail = detail;
        Severity = DigestionReceiptIntegrity.SeverityFor(code);
    }

    internal string Code { get; }

    internal string Detail { get; }

    internal DigestionGapSeverity Severity { get; }
}

internal readonly record struct DigestionReceiptIntegrityGapIdentity(
    string AtomId,
    string Code,
    string Detail);

internal static class DigestionReceiptIntegrity
{
    private static readonly ImmutableHashSet<string> FatalCodes =
        ImmutableHashSet.Create(
            StringComparer.Ordinal,
            "coverage-receipt-mismatch",
            "scribe-definition-mismatch",
            "scribe-emission-mismatch");

    internal static DigestionGapSeverity SeverityFor(string code) =>
        FatalCodes.Contains(code)
            ? DigestionGapSeverity.ReceiptIntegrityFailure
            : DigestionGapSeverity.NonFatal;

    // Baseline directory parsing intentionally omits the derived genre projection. For a
    // fork-point receipt comparison, retain the baseline entries but reuse the candidate's
    // parsed source metadata; deleted sources cannot contribute a candidate-side delta.
    internal static BackfillInventoryDocument ForkPointView(
        BackfillInventoryDocument candidate,
        BackfillInventoryDocument forkPoint)
    {
        var candidateSources = candidate.RequireDigestionSources()
            .ToDictionary(static source => source.SourceId, StringComparer.Ordinal);
        return forkPoint.WithDigestionSources(
            forkPoint.RequireDigestionSources()
                .Where(source => candidateSources.ContainsKey(source.SourceId))
                .Select(source => source with
                {
                    GenreRegistryProjection = candidateSources[source.SourceId].GenreRegistryProjection,
                })
                .ToImmutableArray());
    }

    internal static ImmutableArray<DigestionReceiptIntegrityGapIdentity> Identities(
        DigestionLedgerEvaluation evaluation) =>
        Gaps(evaluation)
            .Select(static item => new DigestionReceiptIntegrityGapIdentity(
                item.Entry.AtomId,
                item.Gap.Code,
                item.Gap.Detail))
            .Distinct()
            .OrderBy(static identity => identity.AtomId, StringComparer.Ordinal)
            .ThenBy(static identity => identity.Code, StringComparer.Ordinal)
            .ThenBy(static identity => identity.Detail, StringComparer.Ordinal)
            .ToImmutableArray();

    internal static ImmutableArray<string> FailureReasons(DigestionLedgerEvaluation evaluation) =>
        Identities(evaluation).Select(Render).ToImmutableArray();

    internal static bool HasFailure(DigestionLedgerEvaluation evaluation) =>
        Identities(evaluation).Length > 0;

    internal static ImmutableArray<string> NewFailureReasons(
        DigestionLedgerEvaluation before,
        DigestionLedgerEvaluation candidate)
        => NewFailureIdentities(before, candidate)
            .Select(Render)
            .ToImmutableArray();

    internal static ImmutableArray<DigestionReceiptIntegrityGapIdentity> NewFailureIdentities(
        DigestionLedgerEvaluation before,
        DigestionLedgerEvaluation candidate)
    {
        var baseline = Identities(before).ToHashSet();
        return Identities(candidate)
            .Where(identity => !baseline.Contains(identity))
            .ToImmutableArray();
    }

    internal static ImmutableHashSet<DigestionReceiptIntegrityGapIdentity> ExactScribeRepairIdentities(
        DigestionLedgerEvaluation evaluation,
        string atomId,
        string gid) =>
        Identities(evaluation)
            .Where(identity => string.Equals(identity.AtomId, atomId, StringComparison.Ordinal)
                && string.Equals(identity.Detail, gid, StringComparison.Ordinal)
                && identity.Code is "scribe-definition-mismatch" or "scribe-emission-mismatch")
            .ToImmutableHashSet();

    internal static string Render(DigestionReceiptIntegrityGapIdentity identity) =>
        $"{identity.AtomId}:{identity.Code}:{identity.Detail}";

    private static IEnumerable<(DigestionLedgerEntry Entry, DigestionGap Gap)> Gaps(
        DigestionLedgerEvaluation evaluation) =>
        evaluation.Entries.SelectMany(static entry => entry.Gaps
            .Where(static gap => gap.Severity == DigestionGapSeverity.ReceiptIntegrityFailure)
            .Select(gap => (entry.Entry, gap)));
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
