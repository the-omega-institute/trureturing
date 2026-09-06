using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record BackfillTicketReference(string CaseId, string Gid);

internal sealed record DigestionCoverageEdge(string Gid, string? TargetStatementId);

internal sealed record DigestionScribeReceipt(
    string Gid,
    string DefinitionSha256,
    string EmissionSha256);

internal sealed record DigestionExternalReceipt(string Path, string Sha256);

internal sealed record DigestionNonpropositional(
    string Justification,
    string? PreviousAtomId,
    string? NextAtomId)
{
    internal bool IsValid => !string.IsNullOrWhiteSpace(Justification)
        && Justification == Justification.Trim()
        && (PreviousAtomId is null || IsAtomId(PreviousAtomId))
        && (NextAtomId is null || IsAtomId(NextAtomId));

    internal static bool IsAtomId(string value) => value.Length == 64
        && value.All(static character => character is >= '0' and <= '9' or >= 'a' and <= 'f');
}

internal sealed record DigestionQuarantine(
    string Justification,
    string ReentryCondition,
    string BlockerClass)
{
    // 封闭字母表:三类均来自 #2137 记录的 21 条实测弹出行
    // (2 already-covered / 7 missing-prerequisite / 12 multi-clause-guard)。
    internal static readonly ImmutableArray<string> BlockerClasses =
        ["already-covered", "missing-prerequisite", "multi-clause-guard"];
}

internal sealed record DigestionDispositionGap(string Code, string Detail);

internal sealed record DigestionCoverDisposition(
    DigestionStatus Outcome,
    ImmutableArray<string> Gids,
    ImmutableArray<DigestionDispositionGap> Gaps);

internal sealed record DigestionReceipts(
    ImmutableArray<DigestionScribeReceipt> Scribe,
    ImmutableArray<string> UnresolvedSubitems,
    ImmutableArray<string> ChainAtoms,
    DigestionExternalReceipt? TailAuthorization,
    DigestionQuarantine? Quarantine = null,
    DigestionCoverDisposition? CoverDisposition = null,
    DigestionNonpropositional? Nonpropositional = null)
{
    internal bool IsEmptyForSourceRevision =>
        Scribe.IsEmpty
        && UnresolvedSubitems.IsEmpty
        && ChainAtoms.IsEmpty
        && TailAuthorization is null
        && Quarantine is null
        && Nonpropositional is null;

    internal bool IsEmpty =>
        IsEmptyForSourceRevision
        && CoverDisposition is null;
}

internal enum DigestionMigrationState
{
    Residual,
    Partial,
    Absorbed,
    Nonpropositional,
}

internal enum DigestionTruthState
{
    Closed,
    Tail,
    Open,
    Inapplicable,
}

internal sealed record DigestionStatus(
    DigestionMigrationState Migration,
    DigestionTruthState Truth);

internal sealed record DigestionLedgerEntry(
    string SourceId,
    string SourcePath,
    string Atomizer,
    string AtomId,
    DigestionFingerprints Fingerprints,
    ImmutableArray<DigestionCoverageEdge> Coverage,
    DigestionReceipts Receipts,
    DigestionStatus ProjectedStatus,
    string CasRef)
{
    internal ImmutableArray<string> CoverageGids =>
        Coverage.Select(static edge => edge.Gid)
            .OrderBy(static gid => gid, StringComparer.Ordinal)
            .ToImmutableArray();
}

internal sealed record GenreRegistryProjection
{
    private readonly GenreRegistryCheck? value;

    private GenreRegistryProjection(GenreRegistryCheck? value) => this.value = value;

    internal static GenreRegistryProjection Unavailable { get; } = new((GenreRegistryCheck?)null);

    internal static GenreRegistryProjection Available(GenreRegistryCheck value)
    {
        ArgumentNullException.ThrowIfNull(value);
        return new GenreRegistryProjection(value);
    }

    internal GenreRegistryCheck RequireAvailable() => value
        ?? throw new InvalidOperationException("genre registry projection is unavailable");
}

internal sealed record DigestionLedgerSource(
    string SourceId,
    string SourcePath,
    string Atomizer,
    ImmutableArray<string> AcknowledgedStale,
    GenreRegistryProjection GenreRegistryProjection,
    ImmutableArray<DigestionLedgerEntry> Entries)
{
    internal GenreRegistryCheck GenreRegistryCheck => GenreRegistryProjection.RequireAvailable();
}
