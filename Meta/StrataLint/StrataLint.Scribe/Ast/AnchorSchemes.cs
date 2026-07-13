using System.Globalization;
using System.Text.RegularExpressions;

namespace StrataLint.Scribe;

public enum AnchorScheme
{
    Gict,
    Pzg,
    Spec,
    Literature,
    Mathlib,
}

public enum TheoryNodeKind
{
    Definition,
    Theorem,
    Section,
    Appendix,
}

public enum MathlibTargetKind
{
    Module,
    Declaration,
}

public sealed record GictEdition
{
    private GictEdition(string value) => Value = value;

    public string Value { get; }

    internal static GictEdition? TryCreate(string value) =>
        CanonicalAnchorSyntax.EditionPattern.IsMatch(value) ? new GictEdition(value) : null;

    public override string ToString() => Value;
}

public sealed record PzgEdition
{
    private PzgEdition(string value) => Value = value;

    public string Value { get; }

    internal static PzgEdition? TryCreate(string value) =>
        CanonicalAnchorSyntax.IntegerEditionPattern.IsMatch(value) ? new PzgEdition(value) : null;

    public override string ToString() => Value;
}

public sealed record SpecEdition
{
    private SpecEdition(string value) => Value = value;

    public string Value { get; }

    internal static SpecEdition? TryCreate(string value) =>
        CanonicalAnchorSyntax.EditionPattern.IsMatch(value) ? new SpecEdition(value) : null;

    public override string ToString() => Value;
}

public sealed record GictDivision
{
    private GictDivision(string value) => Value = value;

    public string Value { get; }

    internal static GictDivision? TryCreate(string value) =>
        CanonicalAnchorSyntax.GictDivisionPattern.IsMatch(value) ? new GictDivision(value) : null;

    public override string ToString() => Value;
}

public sealed record TheoryLabel
{
    private TheoryLabel(string value) => Value = value;

    public string Value { get; }

    internal static TheoryLabel? TryCreateNumber(string value) =>
        CanonicalAnchorSyntax.DottedPositiveIntegerPattern.IsMatch(value)
            ? new TheoryLabel(value)
            : null;

    internal static TheoryLabel? TryCreateSlug(string value) =>
        CanonicalAnchorSyntax.LowerSlugPattern.IsMatch(value) ? new TheoryLabel(value) : null;

    internal static TheoryLabel? TryCreateAppendix(string value) =>
        value is [>= 'A' and <= 'Z'] ? new TheoryLabel(value) : null;

    public override string ToString() => Value;
}

public sealed record SubclaimId
{
    private SubclaimId(string value) => Value = value;

    public string Value { get; }

    internal static SubclaimId? TryCreate(string value) =>
        CanonicalAnchorSyntax.LowerSlugPattern.IsMatch(value) ? new SubclaimId(value) : null;

    public override string ToString() => Value;
}

public sealed record PzgEntryNumber
{
    private PzgEntryNumber(int chapter, int item)
    {
        Chapter = chapter;
        Item = item;
    }

    public int Chapter { get; }

    public int Item { get; }

    internal static PzgEntryNumber? TryCreate(string value)
    {
        if (!CanonicalAnchorSyntax.DottedNonnegativeIntegerPattern.IsMatch(value))
        {
            return null;
        }

        var parts = value.Split('.');
        if (parts.Length != 2
            || !int.TryParse(parts[0], NumberStyles.None, CultureInfo.InvariantCulture, out var chapter)
            || !int.TryParse(parts[1], NumberStyles.None, CultureInfo.InvariantCulture, out var item))
        {
            return null;
        }

        return new PzgEntryNumber(chapter, item);
    }

    public override string ToString() =>
        Chapter.ToString(CultureInfo.InvariantCulture)
        + "."
        + Item.ToString(CultureInfo.InvariantCulture);
}

public sealed record SpecClauseId
{
    private SpecClauseId(string value) => Value = value;

    public string Value { get; }

    internal static SpecClauseId? TryCreate(string value) =>
        CanonicalAnchorSyntax.SpecClausePattern.IsMatch(value) ? new SpecClauseId(value) : null;

    public override string ToString() => Value;
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
    internal static readonly Regex EditionPattern = new(
        "^v(?:0|[1-9][0-9]*)(?:\\.(?:0|[1-9][0-9]*))?$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex IntegerEditionPattern = new(
        "^v(?:0|[1-9][0-9]*)$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex GictDivisionPattern = new(
        "^[IVX]+(?:\\.[1-9][0-9]*)?$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex DottedPositiveIntegerPattern = new(
        "^[1-9][0-9]*(?:\\.[1-9][0-9]*)+$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex DottedNonnegativeIntegerPattern = new(
        "^(?:0|[1-9][0-9]*)\\.(?:0|[1-9][0-9]*)$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex LowerSlugPattern = new(
        "^[a-z][a-z0-9-]*$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex SpecClausePattern = new(
        "^(?:A[1-9][0-9]*|SL-[0-9]{3}|sample-[1-9][0-9]*|(?!(?:a[0-9]+|sl-|sample-))[a-z][a-z0-9-]*)$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex BibKeyPattern = new(
        "^[a-z]+[0-9]{4}[a-z][a-z0-9]*$",
        RegexOptions.CultureInvariant);

    internal static readonly Regex LeanNamePattern = new(
        "^[A-Za-z_][A-Za-z0-9_]*(?:\\.[A-Za-z_][A-Za-z0-9_]*)+$",
        RegexOptions.CultureInvariant);
}
