using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace StrataLint.Engine;

internal static class BackfillInventoryWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

    internal static ImmutableArray<byte> Write(BackfillInventoryDocument document) =>
        Write(document, preserveReceiptSyntax: false);

    internal static ImmutableArray<byte> WriteForIngest(BackfillInventoryDocument document) =>
        Write(document, preserveReceiptSyntax: true);

    internal static ImmutableArray<byte> WriteEntry(DigestionLedgerEntry entry)
    {
        ArgumentNullException.ThrowIfNull(entry);
        var builder = new StringBuilder();
        Line(builder, $"source_id: {Scalar(entry.SourceId)}");
        Line(builder, $"source_path: {Scalar(entry.SourcePath)}");
        Line(builder, $"atomizer: {Scalar(entry.Atomizer)}");
        Entry(builder, entry);
        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    internal static ImmutableArray<RawRepositoryEntry> WriteDirectory(
        BackfillInventoryDocument document)
    {
        ArgumentNullException.ThrowIfNull(document);
        var files = ImmutableArray.CreateBuilder<RawRepositoryEntry>();
        foreach (var source in document.RequireDigestionSources())
        {
            var metadata = new StringBuilder();
            Line(metadata, $"source_id = {Toml(source.SourceId)}");
            Line(metadata, $"path = {Toml(source.SourcePath)}");
            Line(metadata, $"atomizer = {Toml(source.Atomizer)}");
            if (source.AcknowledgedStale.Length > 0)
            {
                Line(metadata, "acknowledged_stale = ["
                    + string.Join(", ", source.AcknowledgedStale.Select(Toml)) + "]");
            }
            files.Add(RawRepositoryEntry.FromText(
                $"{BackfillInventoryLoader.RootPath}{source.SourceId}/source.toml",
                metadata.ToString()));

            foreach (var entry in source.Entries)
            {
                var state = $"{DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}-"
                    + DigestionStatusNames.Truth(entry.ProjectedStatus.Truth);
                files.Add(RawRepositoryEntry.FromText(
                    $"{BackfillInventoryLoader.RootPath}{source.SourceId}/{state}/{entry.AtomId}.yaml",
                    AtomEntry(entry)));
            }
        }

        var tickets = new StringBuilder();
        foreach (var ticket in document.RequireTickets())
        {
            Line(tickets, $"{ticket.CaseId} = {Toml(ticket.Gid)}");
        }
        files.Add(RawRepositoryEntry.FromText(BackfillInventoryLoader.TicketIndexPath, tickets.ToString()));
        return files.ToImmutable();
    }

    private static string AtomEntry(DigestionLedgerEntry entry)
    {
        var builder = new StringBuilder();
        Line(builder, $"ast_path: {Scalar(entry.AstPath)}");
        Line(builder, "fingerprints:");
        Line(builder, $"  raw_sha256: {Scalar(entry.Fingerprints.RawSha256)}");
        Line(builder, $"  normalized_sha256: {Scalar(entry.Fingerprints.NormalizedSha256)}");
        Line(builder, $"cas_ref: {Scalar(entry.CasRef)}");
        if (entry.CoverageGids.Length > 0)
        {
            Strings(builder, "coverage_gids", entry.CoverageGids, 2);
        }
        if (entry.Receipts.Coverage.Length > 0
            || entry.Receipts.Scribe.Length > 0
            || entry.Receipts.UnresolvedSubitems.Length > 0)
        {
            Line(builder, "receipts:");
            CoverageReceiptsAt(builder, entry.Receipts.Coverage, 2);
            ScribeReceiptsAt(builder, entry.Receipts.Scribe, 2);
            Strings(builder, "  unresolved_subitems", entry.Receipts.UnresolvedSubitems, 4);
        }
        return builder.ToString();
    }

    private static void CoverageReceiptsAt(
        StringBuilder builder,
        ImmutableArray<DigestionCoverageReceipt> receipts,
        int indent)
    {
        var prefix = new string(' ', indent);
        Line(builder, receipts.Length == 0 ? $"{prefix}coverage: []" : $"{prefix}coverage:");
        foreach (var receipt in receipts)
        {
            Line(builder, $"{prefix}  - gid: {Scalar(receipt.Gid)}");
            Line(builder, $"{prefix}    source_sha256: {Scalar(receipt.SourceSha256)}");
            Line(builder, $"{prefix}    target_sha256: {Scalar(receipt.TargetSha256)}");
        }
    }

    private static void ScribeReceiptsAt(
        StringBuilder builder,
        ImmutableArray<DigestionScribeReceipt> receipts,
        int indent)
    {
        var prefix = new string(' ', indent);
        Line(builder, receipts.Length == 0 ? $"{prefix}scribe: []" : $"{prefix}scribe:");
        foreach (var receipt in receipts)
        {
            Line(builder, $"{prefix}  - gid: {Scalar(receipt.Gid)}");
            Line(builder, $"{prefix}    definition_sha256: {Scalar(receipt.DefinitionSha256)}");
            Line(builder, $"{prefix}    emission_sha256: {Scalar(receipt.EmissionSha256)}");
        }
    }

    private static string Toml(string value) =>
        "\"" + value.Replace("\\", "\\\\", StringComparison.Ordinal)
            .Replace("\"", "\\\"", StringComparison.Ordinal) + "\"";

    private static ImmutableArray<byte> Write(
        BackfillInventoryDocument document,
        bool preserveReceiptSyntax)
    {
        ArgumentNullException.ThrowIfNull(document);
        var builder = new StringBuilder();
        Line(builder, $"schema_version: {BackfillInventoryLoader.SchemaVersion}");
        Line(builder, $"ledger: {BackfillInventoryLoader.LedgerName}");
        Line(builder, "sources:");
        foreach (var source in document.RequireDigestionSources())
        {
            Line(builder, $"  - source_id: {Scalar(source.SourceId)}");
            Line(builder, $"    path: {Scalar(source.SourcePath)}");
            Line(builder, $"    atomizer: {Scalar(source.Atomizer)}");
            if (source.AcknowledgedStale.Length > 0)
            {
                Strings(builder, "    acknowledged_stale", source.AcknowledgedStale, 6);
            }

            Line(builder, source.Entries.Length == 0 ? "    entries: []" : "    entries:");
            foreach (var entry in source.Entries)
            {
                if (preserveReceiptSyntax && entry.ReceiptSyntax is { } syntax)
                {
                    var receipt = BackfillReceiptPreimage.RewriteStatus(
                        syntax,
                        entry.ProjectedStatus);
                    builder.Append(StrictUtf8.GetString(receipt.AsSpan()));
                }
                else
                {
                    Entry(builder, entry);
                }
            }
        }

        var tickets = document.RequireTickets();
        Line(builder, tickets.Length == 0 ? "ticket_index: []" : "ticket_index:");
        foreach (var ticket in tickets)
        {
            Line(builder, $"  - case_id: {Scalar(ticket.CaseId)}");
            Line(builder, $"    gid: {Scalar(ticket.Gid)}");
        }

        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    private static void Entry(StringBuilder builder, DigestionLedgerEntry entry)
    {
        Line(builder, $"      - atom_id: {Scalar(entry.AtomId)}");
        Line(builder, $"        ast_path: {Scalar(entry.AstPath)}");

        Line(builder, "        fingerprints:");
        Line(builder, $"          raw_sha256: {Scalar(entry.Fingerprints.RawSha256)}");
        Line(builder, $"          normalized_sha256: {Scalar(entry.Fingerprints.NormalizedSha256)}");
        Line(builder, $"        cas_ref: {Scalar(entry.CasRef)}");

        Strings(builder, "        coverage_gids", entry.CoverageGids, 10);
        Line(builder, "        receipts:");
        CoverageReceipts(builder, entry.Receipts.Coverage);
        ScribeReceipts(builder, entry.Receipts.Scribe);
        Strings(builder, "          unresolved_subitems", entry.Receipts.UnresolvedSubitems, 12);
        Line(builder, "        status:");
        Line(
            builder,
            $"          migration: {DigestionStatusNames.Migration(entry.ProjectedStatus.Migration)}");
        Line(builder, $"          truth: {DigestionStatusNames.Truth(entry.ProjectedStatus.Truth)}");
    }

    private static void CoverageReceipts(
        StringBuilder builder,
        ImmutableArray<DigestionCoverageReceipt> receipts)
    {
        if (receipts.Length == 0)
        {
            Line(builder, "          coverage: []");
            return;
        }

        Line(builder, "          coverage:");
        foreach (var receipt in receipts)
        {
            Line(builder, $"            - gid: {Scalar(receipt.Gid)}");
            Line(builder, $"              source_sha256: {Scalar(receipt.SourceSha256)}");
            Line(builder, $"              target_sha256: {Scalar(receipt.TargetSha256)}");
        }
    }

    private static void ScribeReceipts(
        StringBuilder builder,
        ImmutableArray<DigestionScribeReceipt> receipts)
    {
        if (receipts.Length == 0)
        {
            Line(builder, "          scribe: []");
            return;
        }

        Line(builder, "          scribe:");
        foreach (var receipt in receipts)
        {
            Line(builder, $"            - gid: {Scalar(receipt.Gid)}");
            Line(builder, $"              definition_sha256: {Scalar(receipt.DefinitionSha256)}");
            Line(builder, $"              emission_sha256: {Scalar(receipt.EmissionSha256)}");
        }
    }

    private static void Strings(
        StringBuilder builder,
        string key,
        ImmutableArray<string> values,
        int itemIndent)
    {
        if (values.Length == 0)
        {
            Line(builder, key + ": []");
            return;
        }

        Line(builder, key + ":");
        var indent = new string(' ', itemIndent);
        foreach (var value in values)
        {
            Line(builder, indent + "- " + Scalar(value));
        }
    }

    private static string Scalar(string value)
    {
        if (RequiresStringQuotes(value))
        {
            return "'" + value + "'";
        }

        if (string.IsNullOrWhiteSpace(value)
            || value[0] is '-' or '?' or ':' or '!' or '&' or '*' or '#' or '{' or '['
            || value.Contains('\r')
            || value.Contains('\n')
            || value.Contains(" #", StringComparison.Ordinal)
            || char.IsWhiteSpace(value[0])
            || char.IsWhiteSpace(value[^1]))
        {
            throw new FormatException($"BACKFILL scalar cannot be emitted canonically: {value}");
        }

        return value;
    }

    private static bool RequiresStringQuotes(string value) =>
        value is "[]" or "null" or "~" or "|" or "|-" or "|+" or ">" or ">-" or ">+"
        || int.TryParse(
            value,
            NumberStyles.Integer,
            CultureInfo.InvariantCulture,
            out var integer)
        && integer >= 0;

    private static void Line(StringBuilder builder, string value) => builder.Append(value).Append('\n');
}
