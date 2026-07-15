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

internal sealed record DigestionReceipts(
    ImmutableArray<DigestionCoverageReceipt> Coverage,
    ImmutableArray<DigestionScribeReceipt> Scribe,
    ImmutableArray<string> UnresolvedSubitems,
    ImmutableArray<string> ChainAtoms,
    DigestionExternalReceipt? TailAuthorization);

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
    BackfillReceiptSyntax? ReceiptSyntax)
{
    internal DigestionLedgerEntry(
        string sourceId,
        string sourcePath,
        string atomizer,
        string atomId,
        DigestionBoundary boundary,
        DigestionFingerprints fingerprints,
        ImmutableArray<string> coverageGids,
        DigestionReceipts receipts,
        DigestionStatus projectedStatus,
        BackfillReceiptSyntax? receiptSyntax = null)
        : this(
            sourceId,
            sourcePath,
            atomizer,
            atomId,
            boundary?.AstPath ?? throw new ArgumentNullException(nameof(boundary)),
            boundary,
            fingerprints,
            coverageGids,
            receipts,
            projectedStatus,
            receiptSyntax)
    {
    }
}

internal sealed record DigestionLedgerSource(
    string SourceId,
    string SourcePath,
    string Atomizer,
    ImmutableArray<string> AcknowledgedStale,
    ImmutableArray<DigestionLedgerEntry> Entries)
{
    internal DigestionLedgerSource(
        string sourceId,
        string sourcePath,
        string atomizer,
        ImmutableArray<DigestionLedgerEntry> entries)
        : this(sourceId, sourcePath, atomizer, [], entries)
    {
    }
}
