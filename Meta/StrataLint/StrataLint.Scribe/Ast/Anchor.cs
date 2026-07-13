namespace StrataLint.Scribe;

public abstract record Anchor
{
    private protected Anchor() { }

    public abstract AnchorScheme Scheme { get; }

    public abstract string CanonicalString { get; }

    internal string ReferenceLocator =>
        string.Join(' ', CanonicalString.Split('/').Skip(2));

    public static AnchorParseResult TryParseCanonical(string? value)
    {
        if (!TrySplitCanonical(value, out var segments, out var error))
        {
            return new AnchorParseResult.Invalid(error);
        }

        if (segments[0] is not ("gict" or "pzg" or "spec" or "lit" or "mathlib"))
        {
            return new AnchorParseResult.Invalid("Anchor scheme is unknown.");
        }

        Anchor? parsed = segments[0] switch
        {
            "gict" => ParseGict(segments),
            "pzg" => ParsePzg(segments),
            "spec" => ParseSpec(segments),
            "lit" => ParseLiterature(segments),
            "mathlib" => ParseMathlib(segments),
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

    private static GictAnchor? ParseGict(string[] segments)
    {
        if (segments.Length == 4
            && segments[2] == "appendix"
            && GictEdition.TryCreate(segments[1]) is { } appendixEdition
            && TheoryLabel.TryCreateAppendix(segments[3]) is { } appendixLabel)
        {
            return new GictAnchor(
                appendixEdition,
                division: null,
                TheoryNodeKind.Appendix,
                appendixLabel,
                subclaim: null);
        }

        if (segments.Length is not (5 or 6)
            || GictEdition.TryCreate(segments[1]) is not { } edition
            || GictDivision.TryCreate(segments[2]) is not { } division
            || !TryTheoryKind(segments[3], out var kind)
            || kind == TheoryNodeKind.Appendix)
        {
            return null;
        }

        var label = kind is TheoryNodeKind.Section
            ? TheoryLabel.TryCreateSlug(segments[4])
            : TheoryLabel.TryCreateNumber(segments[4]);
        var subclaim = segments.Length == 6 ? SubclaimId.TryCreate(segments[5]) : null;
        if (label is null || segments.Length == 6 && subclaim is null)
        {
            return null;
        }

        return new GictAnchor(edition, division, kind, label, subclaim);
    }

    private static bool TryTheoryKind(string value, out TheoryNodeKind kind)
    {
        kind = value switch
        {
            "definition" => TheoryNodeKind.Definition,
            "theorem" => TheoryNodeKind.Theorem,
            "section" => TheoryNodeKind.Section,
            _ => default,
        };
        return value is "definition" or "theorem" or "section";
    }

    private static PzgAnchor? ParsePzg(string[] segments) =>
        segments.Length == 3
        && PzgEdition.TryCreate(segments[1]) is { } edition
        && PzgEntryNumber.TryCreate(segments[2]) is { } entry
            ? new PzgAnchor(edition, entry)
            : null;

    private static SpecAnchor? ParseSpec(string[] segments) =>
        segments.Length == 3
        && SpecEdition.TryCreate(segments[1]) is { } edition
        && SpecClauseId.TryCreate(segments[2]) is { } clause
            ? new SpecAnchor(edition, clause)
            : null;

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

public sealed record GictAnchor : Anchor
{
    internal GictAnchor(
        GictEdition edition,
        GictDivision? division,
        TheoryNodeKind kind,
        TheoryLabel label,
        SubclaimId? subclaim)
    {
        Edition = edition ?? throw new ArgumentNullException(nameof(edition));
        Division = division;
        Kind = kind;
        Label = label ?? throw new ArgumentNullException(nameof(label));
        Subclaim = subclaim;
        if (kind is TheoryNodeKind.Appendix
            ? division is not null || subclaim is not null
            : division is null)
        {
            throw new ArgumentException("GICT anchor fields form an invalid state.");
        }
    }

    public GictEdition Edition { get; }

    public GictDivision? Division { get; }

    public TheoryNodeKind Kind { get; }

    public TheoryLabel Label { get; }

    public SubclaimId? Subclaim { get; }

    public override AnchorScheme Scheme => AnchorScheme.Gict;

    public override string CanonicalString => Kind is TheoryNodeKind.Appendix
        ? $"gict/{Edition.Value}/appendix/{Label.Value}"
        : $"gict/{Edition.Value}/{Division!.Value}/{KindText(Kind)}/{Label.Value}"
            + (Subclaim is null ? string.Empty : "/" + Subclaim.Value);

    public override string ToString() => CanonicalString;

    private static string KindText(TheoryNodeKind kind) => kind switch
    {
        TheoryNodeKind.Definition => "definition",
        TheoryNodeKind.Theorem => "theorem",
        TheoryNodeKind.Section => "section",
        _ => throw new InvalidOperationException("Appendix has a dedicated canonical form."),
    };
}

public sealed record PzgAnchor : Anchor
{
    internal PzgAnchor(PzgEdition edition, PzgEntryNumber entry)
    {
        Edition = edition ?? throw new ArgumentNullException(nameof(edition));
        Entry = entry ?? throw new ArgumentNullException(nameof(entry));
    }

    public PzgEdition Edition { get; }

    public PzgEntryNumber Entry { get; }

    public override AnchorScheme Scheme => AnchorScheme.Pzg;

    public override string CanonicalString => $"pzg/{Edition.Value}/{Entry}";

    public override string ToString() => CanonicalString;
}

public sealed record SpecAnchor : Anchor
{
    internal SpecAnchor(SpecEdition edition, SpecClauseId clause)
    {
        Edition = edition ?? throw new ArgumentNullException(nameof(edition));
        Clause = clause ?? throw new ArgumentNullException(nameof(clause));
    }

    public SpecEdition Edition { get; }

    public SpecClauseId Clause { get; }

    public override AnchorScheme Scheme => AnchorScheme.Spec;

    public override string CanonicalString => $"spec/{Edition.Value}/{Clause.Value}";

    public override string ToString() => CanonicalString;
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
