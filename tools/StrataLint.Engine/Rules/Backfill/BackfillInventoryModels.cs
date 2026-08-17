using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record BackfillTicketReference(string CaseId, string Gid);

internal sealed record DigestionBoundary(string AstPath, int StartByte, int EndByte);

internal sealed record DigestionCoverageReceipt(
    string Gid,
    string SourceSha256,
    string TargetSha256);

internal sealed record DigestionScribeReceipt(
    string Gid,
    string DefinitionSha256,
    string EmissionSha256);

internal sealed record DigestionExternalReceipt(string Path, string Sha256);

internal sealed record DigestionQuarantine(
    string Justification,
    string ReentryCondition);

internal sealed record DigestionReceipts(
    ImmutableArray<DigestionCoverageReceipt> Coverage,
    ImmutableArray<DigestionScribeReceipt> Scribe,
    ImmutableArray<string> UnresolvedSubitems,
    ImmutableArray<string> ChainAtoms,
    DigestionExternalReceipt? TailAuthorization,
    DigestionQuarantine? Quarantine = null);

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
    BackfillReceiptSyntax? ReceiptSyntax,
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
