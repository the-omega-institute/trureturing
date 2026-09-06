using System.Collections.Immutable;

namespace StrataLint.Engine;

internal enum DigestionIngestStrategy
{
    Align,
    AppendOnly,
}

internal sealed record DigestionIngestObservation(
    string AtomId,
    string SourceId,
    string Kind);

internal sealed record DigestionIngestPlan(
    BackfillInventoryDocument AdmissionDocument,
    DigestionLedgerAlignment Alignment,
    int StaleAcknowledged,
    int ResidualOpenAdded,
    ImmutableArray<DigestionCasObject> CasObjects,
    ImmutableArray<DigestionIngestFallback> Fallbacks,
    ImmutableHashSet<string>? SourceIds = null,
    DigestionIngestStrategy Strategy = DigestionIngestStrategy.Align,
    ImmutableHashSet<string>? NewAtomIds = null,
    ImmutableArray<DigestionIngestObservation> Observations = default)
{
    internal BackfillInventoryDocument Document { get; } = Strategy == DigestionIngestStrategy.AppendOnly
        ? AdmissionDocument
        : DigestionIngestor.NormalizeAtomIdentities(AdmissionDocument, SourceIds);

    internal ImmutableHashSet<string> AddedAtomIds { get; } =
        NewAtomIds ?? ImmutableHashSet<string>.Empty;

    internal ImmutableArray<DigestionIngestObservation> PreservedExisting { get; } =
        Observations.IsDefault ? [] : Observations;
}

internal static class DigestionSourceConflictMarkers
{
    internal const string DiagnosticCode = "INGEST-CONFLICT-MARKER-001";

    internal static int? FindFirstLine(ReadOnlySpan<byte> bytes)
    {
        var start = bytes.Length >= 3
            && bytes[0] == 0xef
            && bytes[1] == 0xbb
            && bytes[2] == 0xbf
                ? 3
                : 0;
        var lineNumber = 1;
        while (true)
        {
            var end = start;
            while (end < bytes.Length
                && bytes[end] != (byte)'\r'
                && bytes[end] != (byte)'\n')
            {
                end++;
            }

            var line = bytes[start..end];
            if (line.StartsWith("<<<<<<< "u8)
                || line.StartsWith("||||||| "u8)
                || line.SequenceEqual("======="u8)
                || line.StartsWith(">>>>>>> "u8))
            {
                return lineNumber;
            }

            if (end == bytes.Length)
            {
                return null;
            }

            if (bytes[end] == (byte)'\r'
                && end + 1 < bytes.Length
                && bytes[end + 1] == (byte)'\n')
            {
                end++;
            }

            start = end + 1;
            lineNumber++;
        }
    }

    internal static string FormatFinding(string sourcePath, int line) =>
        $"{DiagnosticCode} {sourcePath}:{line}: unresolved merge conflict marker in digestion source";
}
