using System.Collections.Immutable;

namespace StrataLint.Engine;

internal sealed record DigestionIngestPlan(
    BackfillInventoryDocument AdmissionDocument,
    DigestionLedgerAlignment Alignment,
    int StaleAcknowledged,
    int ResidualOpenAdded,
    ImmutableArray<DigestionCasObject> CasObjects,
    ImmutableArray<DigestionIngestFallback> Fallbacks,
    ImmutableHashSet<string>? SourceIds = null)
{
    internal BackfillInventoryDocument Document { get; } =
        DigestionIngestor.NormalizeAtomIdentities(AdmissionDocument, SourceIds);
}
