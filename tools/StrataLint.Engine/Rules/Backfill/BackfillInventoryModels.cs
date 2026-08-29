using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record BackfillTicketReference(string CaseId, string Gid);

internal sealed record DigestionBoundary(string AstPath, int StartByte, int EndByte);

internal sealed record DigestionCoverageReceipt(
    string Gid,
    string SourceSha256,
    string TargetStatementId);

internal sealed record DigestionScribeReceipt(
    string Gid,
    string DefinitionSha256,
    string EmissionSha256);

internal sealed record DigestionExternalReceipt(string Path, string Sha256);

internal sealed record DigestionQuarantine(
    string Justification,
    string ReentryCondition,
    // 可选的类型化阻断分类(#2137)。此前隔离只有两个自由文本字段,故「某原子为何不该被
    // 再次提供」不可机器判、不可分类统计——而生产线实测已产出 21 条**已分类**的弹出行。
    // 字母表封闭且取自那批实测数据,不是发明的;未知取值由 loader fail-closed 拒绝。
    // 可选:既有条目无此字段,加载与回写皆须保持其字节不变(见 writer 的 null 分支)。
    string? BlockerClass = null)
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
    ImmutableArray<DigestionDispositionGap> Gaps,
    DateTimeOffset RecordedAtUtc);

internal sealed record DigestionReceipts(
    ImmutableArray<DigestionCoverageReceipt> Coverage,
    ImmutableArray<DigestionScribeReceipt> Scribe,
    ImmutableArray<string> UnresolvedSubitems,
    ImmutableArray<string> ChainAtoms,
    DigestionExternalReceipt? TailAuthorization,
    DigestionQuarantine? Quarantine = null,
    DigestionCoverDisposition? CoverDisposition = null)
{
    internal bool IsEmptyForSourceRevision =>
        Coverage.IsEmpty
        && Scribe.IsEmpty
        && UnresolvedSubitems.IsEmpty
        && ChainAtoms.IsEmpty
        && TailAuthorization is null
        && Quarantine is null;

    internal bool IsEmpty =>
        IsEmptyForSourceRevision
        && CoverDisposition is null;
}

internal enum DigestionMigrationState
{
    Residual,
    Partial,
    Absorbed,
}

internal enum DigestionTruthState
{
    Closed,
    Tail,
    Open,
}

internal sealed record DigestionStatus(
    DigestionMigrationState Migration,
    DigestionTruthState Truth);

internal sealed record DigestionLedgerEntry(
    string SourceId,
    string SourcePath,
    string Atomizer,
    string AtomId,
    string AstPath,
    DigestionBoundary? Boundary,
    DigestionFingerprints Fingerprints,
    ImmutableArray<string> CoverageGids,
    DigestionReceipts Receipts,
    DigestionStatus ProjectedStatus,
    string CasRef);

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
