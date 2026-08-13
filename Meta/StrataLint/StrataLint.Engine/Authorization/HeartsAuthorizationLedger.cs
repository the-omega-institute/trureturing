using System.Collections.Immutable;
using System.Globalization;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal sealed record HeartsAuthorizationEntry(
    string Date,
    string Authorization,
    string StatementName,
    string StatementSha256);

internal static partial class HeartsAuthorizationLedger
{
    internal const string Path = "D5/X_Frontier/HeartsAuthorizations.md";

    internal const string Header = """
        # Hearts Authorizations

        | date | authorization | statement | statement-sha256 |
        |---|---|---|---|
        """ + "\n";

    internal static ImmutableArray<HeartsAuthorizationEntry> Read(string text)
    {
        ArgumentNullException.ThrowIfNull(text);
        if (!text.StartsWith(Header, StringComparison.Ordinal)
            || !text.EndsWith('\n'))
        {
            throw new FormatException("Hearts authorization ledger has a noncanonical header or ending.");
        }

        var entries = ImmutableArray.CreateBuilder<HeartsAuthorizationEntry>();
        foreach (var row in text[Header.Length..].Split('\n')[..^1])
        {
            entries.Add(ReadRow(row));
        }

        return entries.ToImmutable();
    }

    private static HeartsAuthorizationEntry ReadRow(string row)
    {
        var parts = row.Split('|');
        if (parts.Length != 6 || parts[0].Length != 0 || parts[^1].Length != 0)
        {
            throw new FormatException("Hearts authorization ledger row must have exactly four columns.");
        }

        var date = parts[1].Trim();
        var authorization = parts[2].Trim();
        var statementName = parts[3].Trim();
        var statementSha256 = parts[4].Trim();
        if (!string.Equals(
                row,
                $"| {date} | {authorization} | {statementName} | {statementSha256} |",
                StringComparison.Ordinal))
        {
            throw new FormatException("Hearts authorization ledger row is not canonical.");
        }

        if (!DateOnly.TryParseExact(
                date,
                "yyyy-MM-dd",
                CultureInfo.InvariantCulture,
                DateTimeStyles.None,
                out _))
        {
            throw new FormatException("Hearts authorization ledger date must be YYYY-MM-DD.");
        }

        if (authorization.Length == 0)
        {
            throw new FormatException("Hearts authorization ledger authorization must not be empty.");
        }

        if (!StatementNamePattern().IsMatch(statementName))
        {
            throw new FormatException("Hearts authorization ledger statement must be fully qualified.");
        }

        if (!Sha256Pattern().IsMatch(statementSha256))
        {
            throw new FormatException("Hearts authorization ledger statement-sha256 is malformed.");
        }

        return new HeartsAuthorizationEntry(date, authorization, statementName, statementSha256);
    }

    [GeneratedRegex(
        "^[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+$",
        RegexOptions.CultureInvariant)]
    private static partial Regex StatementNamePattern();

    [GeneratedRegex("^[0-9a-f]{64}$", RegexOptions.CultureInvariant)]
    private static partial Regex Sha256Pattern();
}
