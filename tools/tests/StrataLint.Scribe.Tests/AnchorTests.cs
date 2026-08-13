using StrataLint.Engine;

namespace StrataLint.Scribe.Tests;

public sealed class AnchorTests
{
    public static TheoryData<string, Type, AnchorScheme> CanonicalExamples => new()
    {
        { "lit/sos1957threegap", typeof(LiteratureAnchor), AnchorScheme.Literature },
        { "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf", typeof(MathlibAnchor), AnchorScheme.Mathlib },
        { "mathlib/decl/Nat.zeckendorf", typeof(MathlibAnchor), AnchorScheme.Mathlib },
        { "lake/module/Mathlib.Data.Nat.Fib.Zeckendorf", typeof(LakeModuleAnchor), AnchorScheme.Lake },
    };

    [Theory]
    [MemberData(nameof(CanonicalExamples))]
    public void CanonicalAnchorsRoundTripExactly(
        string text,
        Type expectedType,
        AnchorScheme expectedScheme)
    {
        var result = Anchor.TryParseCanonical(text);

        var parsed = Assert.IsType<AnchorParseResult.Parsed>(result).Value;
        Assert.IsType(expectedType, parsed);
        Assert.Equal(expectedScheme, parsed.Scheme);
        Assert.Equal(text, parsed.CanonicalString);
        Assert.Equal(text, parsed.ToString());
        Assert.Equal(parsed, Anchor.ParseCanonical(text));
    }

    public static TheoryData<string> InvalidExamples => new()
    {
        "",
        "lit/Sos1957threegap",
        "lit/sos-1957-threegap",
        "lake/module",
        "lake/module/Mathlib.Data.Nat.Fib.Zeckendorf/extra",
        "lake/decl/Nat.zeckendorf",
        "lake/module/Mathlib..Zeckendorf",
        "mathlib/symbol/Nat.zeckendorf",
        "mathlib/module/Mathlib..Zeckendorf",
        "gict/module/Gict.Core",
        "pzg/module/Pzg.Core",
        "spec/module/Spec.Core",
        "batteries/module/Batteries.Data.Array.Lemmas",
        "unknown/value",
    };

    [Theory]
    [MemberData(nameof(InvalidExamples))]
    public void CanonicalParserRejectsMalformedOrNoncanonicalText(string text)
    {
        var result = Anchor.TryParseCanonical(text);

        Assert.IsType<AnchorParseResult.Invalid>(result);
        Assert.Throws<FormatException>(() => Anchor.ParseCanonical(text));
    }

    [Fact]
    public void ParserDistinguishesUnknownSchemeFromMalformedExternalPayload()
    {
        var unknown = Assert.IsType<AnchorParseResult.Invalid>(
            Anchor.TryParseCanonical("unknown/value"));
        var malformed = Assert.IsType<AnchorParseResult.Invalid>(
            Anchor.TryParseCanonical("lit/sos-1957-threegap"));

        Assert.NotEqual(unknown.Message, malformed.Message);
    }

    [Fact]
    public void RetiredInternalSchemesAreUnknown()
    {
        var retired = new[]
        {
            string.Concat("gi", "ct/v9.0/I/theorem/1.0"),
            string.Concat("pz", "g/v9/1.0"),
            string.Concat("sp", "ec/v9/SL-001"),
        };

        Assert.All(retired, value => Assert.IsType<AnchorParseResult.Invalid>(
            Anchor.TryParseCanonical(value)));
    }

    [Fact]
    public void ExternalFamilyUsesTheCanonicalSchemeSet()
    {
        Assert.True(Anchor.IsExternalFamily("lit/sos1957threegap"));
        Assert.True(Anchor.IsExternalFamily(
            string.Concat("mathlib", "/module/Mathlib.Data.Nat.Fib.Basic")));
        Assert.True(Anchor.IsExternalFamily("lake/module/Mathlib.Data.Nat.Fib.Zeckendorf"));
        Assert.False(Anchor.IsExternalFamily("gict/module/Gict.Core"));
        Assert.False(Anchor.IsExternalFamily("pzg/module/Pzg.Core"));
        Assert.False(Anchor.IsExternalFamily("spec/module/Spec.Core"));
        Assert.False(Anchor.IsExternalFamily("batteries/module/Batteries.Data.Array.Lemmas"));
    }

    [Fact]
    public void ParsedAnchorsUseOrdinalValueEquality()
    {
        var first = Anchor.ParseCanonical("lit/sos1957threegap");
        var second = Anchor.ParseCanonical("lit/sos1957threegap");

        Assert.Equal(first, second);
        Assert.Equal(first.GetHashCode(), second.GetHashCode());
    }

    [Fact]
    public void DefinitionDslDoesNotInjectAnImplicitAnchor()
    {
        var header = DefinitionDsl.Header("D5/S1/Phase/Basic", "Explicit provenance only.");

        Assert.Empty(header.Anchors);
    }

    [Fact]
    public void AnchorSubtypesCannotBeConstructedThroughAPublicConstructor()
    {
        var subtypes = new[]
        {
            typeof(LiteratureAnchor),
            typeof(MathlibAnchor),
            typeof(LakeModuleAnchor),
        };

        Assert.All(subtypes, static type => Assert.Empty(type.GetConstructors()));
    }
}
