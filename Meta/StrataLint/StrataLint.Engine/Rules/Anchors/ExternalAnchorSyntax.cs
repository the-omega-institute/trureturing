using System.Text.RegularExpressions;

namespace StrataLint.Engine;

internal static class ExternalAnchorSyntax
{
    private static readonly Regex BibKeyPattern = new(
        "^[a-z]+[0-9]{4}[a-z][a-z0-9]*$",
        RegexOptions.CultureInvariant);
    private static readonly Regex LeanNamePattern = new(
        "^[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+$",
        RegexOptions.CultureInvariant);

    internal static bool IsCanonical(string value)
    {
        var segments = value.Split('/');
        return segments switch
        {
            ["lit", var bibKey] => BibKeyPattern.IsMatch(bibKey),
            ["mathlib", "module" or "decl", var name] => LeanNamePattern.IsMatch(name),
            _ => false,
        };
    }

    internal static bool IsExternalFamily(string value) =>
        value.StartsWith("lit/", StringComparison.Ordinal)
        || value.StartsWith("mathlib/", StringComparison.Ordinal);
}
