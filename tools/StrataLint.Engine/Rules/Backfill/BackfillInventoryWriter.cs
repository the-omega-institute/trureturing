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

    internal static ImmutableArray<byte> WriteAtom(DigestionLedgerEntry entry)
    {
        ArgumentNullException.ThrowIfNull(entry);
        var builder = new StringBuilder();
        if (entry.Boundary is { } boundary)
        {
            Line(builder, "boundary:");
            Line(builder, $"  ast_path: {Scalar(boundary.AstPath)}");
            Line(builder, $"  start_byte: {boundary.StartByte}");
            Line(builder, $"  end_byte: {boundary.EndByte}");
        }
        else
        {
            Line(builder, $"ast_path: {Scalar(entry.AstPath)}");
        }

        Line(builder, "fingerprints:");
        Line(builder, $"  raw_sha256: {Scalar(entry.Fingerprints.RawSha256)}");
        Line(builder, $"  normalized_sha256: {Scalar(entry.Fingerprints.NormalizedSha256)}");
        Line(builder, $"cas_ref: {Scalar(entry.CasRef)}");
        Strings(builder, "coverage_gids", entry.CoverageGids, 2);
        Line(builder, "receipts:");
        AtomCoverageReceipts(builder, entry.Receipts.Coverage);
        AtomScribeReceipts(builder, entry.Receipts.Scribe);
        Strings(builder, "  unresolved_subitems", entry.Receipts.UnresolvedSubitems, 4);
        AtomQuarantine(builder, entry.Receipts.Quarantine);
        if (entry.Receipts.ChainAtoms.Length > 0)
        {
            Strings(builder, "  chain_atoms", entry.Receipts.ChainAtoms, 4);
        }

        if (entry.Receipts.TailAuthorization is { } tail)
        {
            Line(builder, "  tail_authorization:");
            Line(builder, $"    path: {Scalar(tail.Path)}");
            Line(builder, $"    sha256: {Scalar(tail.Sha256)}");
        }

        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    internal static ImmutableArray<byte> WriteSourceMetadata(DigestionLedgerSource source)
    {
        ArgumentNullException.ThrowIfNull(source);
        var builder = new StringBuilder();
        Line(builder, $"source_id = {TomlScalar(source.SourceId)}");
        Line(builder, $"path = {TomlScalar(source.SourcePath)}");
        Line(builder, $"atomizer = {TomlScalar(source.Atomizer)}");
        if (source.AcknowledgedStale.Length > 0)
        {
            Line(
                builder,
                "acknowledged_stale = ["
                + string.Join(", ", source.AcknowledgedStale.Select(TomlScalar))
                + "]");
        }

        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

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
            EnsureLineBreak(builder);
            Line(builder, $"  - source_id: {Scalar(source.SourceId)}");
            Line(builder, $"    path: {Scalar(source.SourcePath)}");
            Line(builder, $"    atomizer: {Scalar(source.Atomizer)}");
            if (source.AcknowledgedStale.Length > 0
                || source.Entries.Any(static entry => entry.Boundary is null))
            {
                Strings(builder, "    acknowledged_stale", source.AcknowledgedStale, 6);
            }

            Line(builder, source.Entries.Length == 0 ? "    entries: []" : "    entries:");
            foreach (var entry in source.Entries)
            {
                EnsureLineBreak(builder);
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

        return ImmutableArray.CreateRange(StrictUtf8.GetBytes(builder.ToString()));
    }

    private static void EnsureLineBreak(StringBuilder builder)
    {
        if (builder.Length > 0 && builder[^1] != '\n')
        {
            builder.Append('\n');
        }
    }

    private static void Entry(StringBuilder builder, DigestionLedgerEntry entry)
    {
        Line(builder, $"      - atom_id: {Scalar(entry.AtomId)}");
        if (entry.Boundary is { } boundary)
        {
            Line(builder, "        boundary:");
            Line(builder, $"          ast_path: {Scalar(boundary.AstPath)}");
            Line(builder, $"          start_byte: {boundary.StartByte}");
            Line(builder, $"          end_byte: {boundary.EndByte}");
        }
        else
        {
            Line(builder, $"        ast_path: {Scalar(entry.AstPath)}");
        }

        Line(builder, "        fingerprints:");
        Line(builder, $"          raw_sha256: {Scalar(entry.Fingerprints.RawSha256)}");
        Line(builder, $"          normalized_sha256: {Scalar(entry.Fingerprints.NormalizedSha256)}");
        Line(builder, $"        cas_ref: {Scalar(entry.CasRef)}");

        Strings(builder, "        coverage_gids", entry.CoverageGids, 10);
        Line(builder, "        receipts:");
        CoverageReceipts(builder, entry.Receipts.Coverage);
        ScribeReceipts(builder, entry.Receipts.Scribe);
        Strings(builder, "          unresolved_subitems", entry.Receipts.UnresolvedSubitems, 12);
        Quarantine(builder, entry.Receipts.Quarantine);
        Strings(builder, "          chain_atoms", entry.Receipts.ChainAtoms, 12);
        if (entry.Receipts.TailAuthorization is { } tail)
        {
            Line(builder, "          tail_authorization:");
            Line(builder, $"            path: {Scalar(tail.Path)}");
            Line(builder, $"            sha256: {Scalar(tail.Sha256)}");
        }
        else
        {
            Line(builder, "          tail_authorization: null");
        }

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

    private static void AtomCoverageReceipts(
        StringBuilder builder,
        ImmutableArray<DigestionCoverageReceipt> receipts)
    {
        if (receipts.Length == 0)
        {
            Line(builder, "  coverage: []");
            return;
        }

        Line(builder, "  coverage:");
        foreach (var receipt in receipts)
        {
            Line(builder, $"    - gid: {Scalar(receipt.Gid)}");
            Line(builder, $"      source_sha256: {Scalar(receipt.SourceSha256)}");
            Line(builder, $"      target_sha256: {Scalar(receipt.TargetSha256)}");
        }
    }

    private static void AtomScribeReceipts(
        StringBuilder builder,
        ImmutableArray<DigestionScribeReceipt> receipts)
    {
        if (receipts.Length == 0)
        {
            Line(builder, "  scribe: []");
            return;
        }

        Line(builder, "  scribe:");
        foreach (var receipt in receipts)
        {
            Line(builder, $"    - gid: {Scalar(receipt.Gid)}");
            Line(builder, $"      definition_sha256: {Scalar(receipt.DefinitionSha256)}");
            Line(builder, $"      emission_sha256: {Scalar(receipt.EmissionSha256)}");
        }
    }

    private static void AtomQuarantine(StringBuilder builder, DigestionQuarantine? quarantine)
    {
        if (quarantine is null)
        {
            return;
        }

        Line(builder, "  quarantine:");
        Line(builder, $"    justification: {Scalar(quarantine.Justification)}");
        Line(builder, $"    reentry_condition: {Scalar(quarantine.ReentryCondition)}");
    }

    private static void Quarantine(StringBuilder builder, DigestionQuarantine? quarantine)
    {
        if (quarantine is null)
        {
            return;
        }

        Line(builder, "          quarantine:");
        Line(builder, $"            justification: {Scalar(quarantine.Justification)}");
        Line(builder, $"            reentry_condition: {Scalar(quarantine.ReentryCondition)}");
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

    private static string TomlScalar(string value)
    {
        if (string.IsNullOrWhiteSpace(value)
            || value.Contains('"', StringComparison.Ordinal)
            || value.Contains('\r', StringComparison.Ordinal)
            || value.Contains('\n', StringComparison.Ordinal))
        {
            throw new FormatException($"digestion source metadata scalar cannot be emitted canonically: {value}");
        }

        return $"\"{value}\"";
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
