using System.Diagnostics.CodeAnalysis;
using System.Text.RegularExpressions;

namespace StrataLint.Engine;

public sealed record Doi
{
    private static readonly Regex Pattern = new(
        "^10\\.[0-9]{4,9}/\\S+$",
        RegexOptions.IgnoreCase | RegexOptions.CultureInvariant);

    private Doi(string value) => Value = value;

    public string Value { get; }

    public static Doi Create(string value) => TryCreate(value, out var doi)
        ? doi
        : throw new ArgumentException("DOI is malformed or noncanonical.", nameof(value));

    public static bool TryCreate(string? value, [NotNullWhen(true)] out Doi? doi)
    {
        if (value is not null
            && value.Length > 0
            && string.Equals(value, value.Trim(), StringComparison.Ordinal)
            && value.IndexOfAny(['\r', '\n']) < 0
            && Pattern.IsMatch(value))
        {
            doi = new Doi(value);
            return true;
        }

        doi = null;
        return false;
    }

    public override string ToString() => Value;
}
