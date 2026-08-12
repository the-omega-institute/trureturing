namespace StrataLint.Engine;

public abstract record Anchor
{
    private protected Anchor() { }

    public abstract AnchorScheme Scheme { get; }

    public abstract string CanonicalString { get; }

    // The external schemes are named here and nowhere else. A caller asking "is this
    // string in the external family?" must not re-spell the prefixes: that is how the
    // duplicated anchor grammar (the deleted ExternalAnchorSyntax) came about.
    public static bool IsExternalFamily(string? value)
    {
        if (value is null)
        {
            return false;
        }

        var separator = value.IndexOf('/');
        return separator > 0 && ParseScheme(value[..separator]) is not null;
    }

    public static AnchorParseResult TryParseCanonical(string? value)
    {
        if (!TrySplitCanonical(value, out var segments, out var error))
        {
            return new AnchorParseResult.Invalid(error);
        }

        if (ParseScheme(segments[0]) is not { } scheme)
        {
            return new AnchorParseResult.Invalid("Anchor scheme is unknown.");
        }

        Anchor? parsed = scheme switch
        {
            CanonicalScheme.Literature => ParseLiterature(segments),
            CanonicalScheme.Mathlib => ParseMathlib(segments),
            CanonicalScheme.Lake => ParseLake(segments),
            _ => throw new System.Diagnostics.UnreachableException(),
        };

        if (parsed is null)
        {
            return new AnchorParseResult.Invalid("Anchor scheme payload is invalid.");
        }

        return string.Equals(parsed.CanonicalString, value, StringComparison.Ordinal)
            ? new AnchorParseResult.Parsed(parsed)
            : new AnchorParseResult.Invalid("Anchor is not canonical.");
    }

    public static Anchor ParseCanonical(string value) =>
        TryParseCanonical(value) is AnchorParseResult.Parsed parsed
            ? parsed.Value
            : throw new FormatException("Anchor is malformed or noncanonical.");

    public override string ToString() => CanonicalString;

    private enum CanonicalScheme
    {
        Literature,
        Mathlib,
        Lake,
    }

    private static CanonicalScheme? ParseScheme(string value) => value switch
    {
        "lit" => CanonicalScheme.Literature,
        "mathlib" => CanonicalScheme.Mathlib,
        "lake" => CanonicalScheme.Lake,
        _ => null,
    };

    private static bool TrySplitCanonical(
        string? value,
        out string[] segments,
        out string error)
    {
        segments = [];
        error = "Anchor is empty.";
        if (string.IsNullOrEmpty(value))
        {
            return false;
        }

        foreach (var character in value)
        {
            if (!IsAnchorCharacter(character))
            {
                error = "Anchor contains a non-ASCII or forbidden character.";
                return false;
            }
        }

        segments = value.Split('/');
        if (segments.Length < 2
            || segments.Any(static segment => segment.Length == 0 || segment is "." or ".."))
        {
            error = "Anchor contains an empty or dot segment.";
            return false;
        }

        error = string.Empty;
        return true;
    }

    private static bool IsAnchorCharacter(char value) =>
        value is >= 'A' and <= 'Z'
            or >= 'a' and <= 'z'
            or >= '0' and <= '9'
            or '_' or '/' or '.' or '-';

    private static LiteratureAnchor? ParseLiterature(string[] segments) =>
        segments.Length == 2 && BibKey.TryCreate(segments[1]) is { } bibKey
            ? new LiteratureAnchor(bibKey)
            : null;

    private static MathlibAnchor? ParseMathlib(string[] segments)
    {
        if (segments.Length != 3 || LeanQualifiedName.TryCreate(segments[2]) is not { } name)
        {
            return null;
        }

        return segments[1] switch
        {
            "module" => new MathlibAnchor(MathlibTargetKind.Module, name),
            "decl" => new MathlibAnchor(MathlibTargetKind.Declaration, name),
            _ => null,
        };
    }

    private static LakeModuleAnchor? ParseLake(string[] segments) =>
        segments.Length == 3
        && segments[1] == "module"
        && LeanQualifiedName.TryCreate(segments[2]) is { } name
            ? new LakeModuleAnchor(name)
            : null;
}

public abstract record AnchorParseResult
{
    private AnchorParseResult() { }

    public sealed record Parsed : AnchorParseResult
    {
        internal Parsed(Anchor value) =>
            Value = value ?? throw new ArgumentNullException(nameof(value));

        public Anchor Value { get; }
    }

    public sealed record Invalid : AnchorParseResult
    {
        internal Invalid(string message) => Message = message;

        public string Message { get; }
    }
}

public sealed record LiteratureAnchor : Anchor
{
    internal LiteratureAnchor(BibKey bibKey) =>
        BibKey = bibKey ?? throw new ArgumentNullException(nameof(bibKey));

    public BibKey BibKey { get; }

    public override AnchorScheme Scheme => AnchorScheme.Literature;

    public override string CanonicalString => $"lit/{BibKey.Value}";

    public override string ToString() => CanonicalString;
}

public sealed record LakeModuleAnchor : Anchor
{
    internal LakeModuleAnchor(LeanQualifiedName name) =>
        Name = name ?? throw new ArgumentNullException(nameof(name));

    public LeanQualifiedName Name { get; }

    public override AnchorScheme Scheme => AnchorScheme.Lake;

    public override string CanonicalString => $"lake/module/{Name.Value}";

    public override string ToString() => CanonicalString;
}

public sealed record MathlibAnchor : Anchor
{
    internal MathlibAnchor(MathlibTargetKind targetKind, LeanQualifiedName name)
    {
        if (targetKind is not (MathlibTargetKind.Module or MathlibTargetKind.Declaration))
        {
            throw new ArgumentOutOfRangeException(nameof(targetKind));
        }

        TargetKind = targetKind;
        Name = name ?? throw new ArgumentNullException(nameof(name));
    }

    public MathlibTargetKind TargetKind { get; }

    public LeanQualifiedName Name { get; }

    public override AnchorScheme Scheme => AnchorScheme.Mathlib;

    public override string CanonicalString =>
        $"mathlib/{(TargetKind is MathlibTargetKind.Module ? "module" : "decl")}/{Name.Value}";

    public override string ToString() => CanonicalString;
}
