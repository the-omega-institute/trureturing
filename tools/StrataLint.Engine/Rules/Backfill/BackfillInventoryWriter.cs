using System.Collections.Immutable;
using System.Globalization;
using System.Text;

namespace StrataLint.Engine;

internal static class BackfillInventoryWriter
{
    private static readonly UTF8Encoding StrictUtf8 = new(false, true);

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
        CoverDisposition(builder, entry.Receipts.CoverDisposition, "  ");
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
        ValidateGenreRegistryCheck(source.GenreRegistryCheck);
        var builder = new StringBuilder();
        Line(builder, $"source_id = {TomlScalar(source.SourceId)}");
        Line(builder, $"path = {TomlScalar(source.SourcePath)}");
        Line(builder, $"atomizer = {TomlScalar(source.Atomizer)}");
        Line(
            builder,
            $"genre_registry_check = {TomlScalar(GenreRegistryCheckNames.Render(source.GenreRegistryCheck.Kind))}");
        Line(
            builder,
            "unregistered_genres = ["
            + string.Join(", ", source.GenreRegistryCheck.UnregisteredGenres.Select(TomlGenreToken))
            + "]");
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

    internal static ImmutableArray<byte> WriteStatusAuthorityIdentity(
        DigestionLedgerSource source,
        DigestionLedgerEntry entry) =>
        [.. WriteSourceMetadata(source with { AcknowledgedStale = [] }), .. WriteEntry(entry)];

    private static void ValidateGenreRegistryCheck(GenreRegistryCheck check)
    {
        ArgumentNullException.ThrowIfNull(check);
        var tokens = check.UnregisteredGenres;
        if (tokens.Any(string.IsNullOrWhiteSpace)
            || !tokens.SequenceEqual(
                tokens.Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal),
                StringComparer.Ordinal))
        {
            throw new InvalidOperationException(
                "unregistered genres must contain sorted unique nonempty tokens");
        }

        if (check.Kind == GenreRegistryCheckKind.NoRegistry && !tokens.IsEmpty)
        {
            throw new InvalidOperationException(
                "no-registry requires empty unregistered genres");
        }
    }

    private static void Entry(StringBuilder builder, DigestionLedgerEntry entry)
    {
        Line(builder, $"      - atom_id: {Scalar(entry.AtomId)}");
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
        CoverDisposition(builder, entry.Receipts.CoverDisposition, "          ");
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
            Line(builder, $"              target_statement_id: {Scalar(receipt.TargetStatementId)}");
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
            Line(builder, $"      target_statement_id: {Scalar(receipt.TargetStatementId)}");
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
        // 仅在有值时输出:既有条目无 blocker_class,若无条件写出会改动其字节,
        // 导致全量账本 churn 并连带触发 SL-008 材料漂移。
        if (quarantine.BlockerClass is { } blockerClass)
        {
            Line(builder, $"    blocker_class: {Scalar(blockerClass)}");
        }
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
        if (quarantine.BlockerClass is { } nestedBlockerClass)
        {
            Line(builder, $"            blocker_class: {Scalar(nestedBlockerClass)}");
        }
    }

    private static void CoverDisposition(
        StringBuilder builder,
        DigestionCoverDisposition? disposition,
        string indent)
    {
        if (disposition is null)
        {
            return;
        }

        Line(builder, indent + "cover_disposition:");
        Line(
            builder,
            indent + "  outcome: " + Scalar(
                DigestionStatusNames.Migration(disposition.Outcome.Migration)
                + "-"
                + DigestionStatusNames.Truth(disposition.Outcome.Truth)));
        Line(
            builder,
            indent + "  recorded_at_utc: "
            + Scalar(disposition.RecordedAtUtc.ToString("O", CultureInfo.InvariantCulture)));
        Line(builder, indent + "  gids:");
        foreach (var gid in disposition.Gids)
        {
            Line(builder, indent + "    - " + Scalar(gid));
        }

        if (disposition.Gaps.IsEmpty)
        {
            Line(builder, indent + "  gaps: []");
            return;
        }

        Line(builder, indent + "  gaps:");
        foreach (var gap in disposition.Gaps)
        {
            Line(builder, indent + "    - code: " + Scalar(gap.Code));
            Line(builder, indent + "      detail: " + Scalar(gap.Detail));
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
        if (RequiresStringQuotes(value)
            || value.Contains(": ", StringComparison.Ordinal))
        {
            if (value.Contains('\'', StringComparison.Ordinal))
            {
                throw new FormatException($"BACKFILL quoted scalar cannot contain a single quote: {value}");
            }

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

    private static string TomlGenreToken(string value)
    {
        var builder = new StringBuilder(value.Length + 2);
        builder.Append('"');
        foreach (var character in value)
        {
            switch (character)
            {
                case '"': builder.Append("\\\""); break;
                case '\\': builder.Append("\\\\"); break;
                case '\b': builder.Append("\\b"); break;
                case '\t': builder.Append("\\t"); break;
                case '\n': builder.Append("\\n"); break;
                case '\f': builder.Append("\\f"); break;
                case '\r': builder.Append("\\r"); break;
                default:
                    if (character < ' ' || character == '\u007f')
                    {
                        builder.Append("\\u")
                            .Append(((int)character).ToString("X4", CultureInfo.InvariantCulture));
                    }
                    else
                    {
                        builder.Append(character);
                    }
                    break;
            }
        }

        return builder.Append('"').ToString();
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
