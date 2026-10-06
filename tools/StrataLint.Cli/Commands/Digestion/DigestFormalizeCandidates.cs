using System.Text.Encodings.Web;
using System.Text.Json;
using StrataLint.Engine;

namespace StrataLint.Cli;

internal static class DigestFormalizeCandidates
{
    private static readonly JsonSerializerOptions JsonOptions = new()
    {
        WriteIndented = true,
        PropertyNamingPolicy = JsonNamingPolicy.SnakeCaseLower,
        Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping,
    };

    internal static string Render(
        DigestionFrontierProjection frontier,
        RepositorySnapshot snapshot,
        BackfillInventoryDocument ledger,
        string? selectedAtomId)
    {
        ArgumentNullException.ThrowIfNull(frontier);
        ArgumentNullException.ThrowIfNull(snapshot);
        ArgumentNullException.ThrowIfNull(ledger);
        var projections = frontier.Entries
            .Where(item => selectedAtomId is null
                || string.Equals(item.Entry.AtomId, selectedAtomId, StringComparison.Ordinal))
            .Select(item => Project(item, snapshot))
            .Where(static item => item is not null)
            .OrderBy(static item => item!.SourceId, StringComparer.Ordinal)
            .ThenBy(static item => item!.AtomId, StringComparer.Ordinal)
            .Select(static item => item!)
            .ToArray();
        var material = new
        {
            schema = "stratalint-formalize-candidates-v5",
            ledger_sha256 = DigestionLedgerPreimage.ComputeSha256(ledger),
            candidates = projections
                .Where(static item => item.Candidate is not null)
                .Select(static item => item.Candidate!),
            quarantined = projections
                .Where(static item => item.Quarantined is not null)
                .Select(static item => item.Quarantined!),
            withheld = projections
                .Where(static item => item.Withheld is not null)
                .Select(static item => item.Withheld!),
        };
        return JsonSerializer.Serialize(material, JsonOptions) + "\n";
    }

    internal static FormalizeProjection? Project(
        DigestionFrontierEntry frontier,
        RepositorySnapshot snapshot) => frontier.PrimaryDisposition switch
    {
        DigestionFrontierDisposition.Quarantined => ProjectQuarantined(frontier),
        DigestionFrontierDisposition.Withheld => ProjectWithheld(frontier),
        DigestionFrontierDisposition.ChainChild => null,
        DigestionFrontierDisposition.NotFormalizable => null,
        DigestionFrontierDisposition.FormalizableClaim => ProjectFormalizable(frontier, snapshot),
        _ => throw DigestionFrontierDispositionPolicy.Unsupported(frontier.PrimaryDisposition),
    };

    private static FormalizeProjection ProjectFormalizable(
        DigestionFrontierEntry frontier,
        RepositorySnapshot snapshot)
    {
        var entry = frontier.Entry;
        // Candidate projection is an index for the next AI action.  Fetch the
        // selected atom with show-atom when text is needed; constructing this
        // list must not read every candidate blob from CAS.
        return new FormalizeProjection(
            entry.SourceId,
            entry.AtomId,
            new FormalizeCandidate(
                entry.SourceId,
                entry.AtomId,
                frontier.KindLabel,
                entry.CasRef,
                entry.Fingerprints.RawSha256,
                string.Empty),
            null,
            null);
    }

    private static FormalizeProjection ProjectQuarantined(DigestionFrontierEntry frontier)
    {
        var entry = frontier.Entry;
        var quarantine = entry.Receipts.Quarantine!;
        return new FormalizeProjection(
            entry.SourceId,
            entry.AtomId,
            null,
            new QuarantinedFormalizeCandidate(
                entry.SourceId,
                entry.AtomId,
                quarantine.Justification,
                quarantine.ReentryCondition,
                quarantine.BlockerClass),
            null);
    }

    private static FormalizeProjection ProjectWithheld(DigestionFrontierEntry frontier)
    {
        var entry = frontier.Entry;
        return new FormalizeProjection(
            entry.SourceId,
            entry.AtomId,
            null,
            null,
            new WithheldFormalizeCandidate(
                entry.AtomId,
                frontier.PrimaryDetail,
                frontier.StatusQualifier));
    }

    internal sealed record FormalizeCandidate(
        string SourceId,
        string AtomId,
        string Kind,
        string CasRef,
        string RawSha256,
        string AtomText);

    internal sealed record WithheldFormalizeCandidate(
        string AtomId,
        string WithholdReason,
        string? StatusQualifier);

    internal sealed record QuarantinedFormalizeCandidate(
        string SourceId,
        string AtomId,
        string Justification,
        string ReentryCondition,
        string BlockerClass);

    internal sealed record FormalizeProjection(
        string SourceId,
        string AtomId,
        FormalizeCandidate? Candidate,
        QuarantinedFormalizeCandidate? Quarantined,
        WithheldFormalizeCandidate? Withheld);
}
