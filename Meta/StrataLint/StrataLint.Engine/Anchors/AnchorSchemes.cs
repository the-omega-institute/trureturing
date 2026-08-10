using System.Text.RegularExpressions;

namespace StrataLint.Engine;

public enum AnchorScheme
{
    Literature,
    Mathlib,
}

public enum MathlibTargetKind
{
    Module,
    Declaration,
}


public sealed record BibKey
{
    private BibKey(string value) => Value = value;

    public string Value { get; }

    internal static BibKey? TryCreate(string value) =>
        CanonicalAnchorSyntax.BibKeyPattern.IsMatch(value) ? new BibKey(value) : null;

    public override string ToString() => Value;
}

public sealed record LeanQualifiedName
{
    private LeanQualifiedName(string value) => Value = value;

    public string Value { get; }

    internal static LeanQualifiedName? TryCreate(string value) =>
        CanonicalAnchorSyntax.LeanNamePattern.IsMatch(value) ? new LeanQualifiedName(value) : null;

    public override string ToString() => Value;
}

internal static class CanonicalAnchorSyntax
{
    internal static readonly Regex BibKeyPattern = new(
        "^[a-z]+[0-9]{4}[a-z][a-z0-9]*$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex LeanNamePattern = new(
        "^[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+$",
        RegexOptions.CultureInvariant);
}
