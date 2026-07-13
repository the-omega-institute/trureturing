using StrataLint.Scribe;

namespace StrataLint.Scribe.Tests;

public sealed class AnchorTests
{
    public static TheoryData<string, Type, AnchorScheme> CanonicalExamples => new()
    {
        { "gict/v3.6/I.2/definition/1.4", typeof(GictAnchor), AnchorScheme.Gict },
        { "gict/v3.6/I.1/theorem/1.3/iii", typeof(GictAnchor), AnchorScheme.Gict },
        { "gict/v3.6/VIII/section/hearts", typeof(GictAnchor), AnchorScheme.Gict },
        { "gict/v3.6/appendix/A", typeof(GictAnchor), AnchorScheme.Gict },
        { "pzg/v170/26.4", typeof(PzgAnchor), AnchorScheme.Pzg },
        { "pzg/v170/0.0", typeof(PzgAnchor), AnchorScheme.Pzg },
        { "spec/v7.11/SL-017", typeof(SpecAnchor), AnchorScheme.Spec },
        { "spec/v7.11/sample-11", typeof(SpecAnchor), AnchorScheme.Spec },
        { "lit/sos1957threegap", typeof(LiteratureAnchor), AnchorScheme.Literature },
        { "mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf", typeof(MathlibAnchor), AnchorScheme.Mathlib },
        { "mathlib/decl/Nat.zeckendorf", typeof(MathlibAnchor), AnchorScheme.Mathlib },
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
        "GICT/v3.6/I.2/definition/1.4",
        "gict//v3.6/I.2/definition/1.4",
        "gict/v3.6/I.2/definition/1.4/",
        "gict/v3.6/../definition/1.4",
        "gict/v3.6/I.2/definitions/1.1-1.2",
        "gict/v3.6/I.2/theorem/01.3",
        "pzg/v170/26.04",
        "pzg/v170/00.0",
        "spec/v7.11/sl-017",
        "lit/Sos1957threegap",
        "lit/sos-1957-threegap",
        "mathlib/symbol/Nat.zeckendorf",
        "mathlib/module/Mathlib..Zeckendorf",
        "spec/v7.11/SL-017%20",
        "spec/v7.11/SL-０１７",
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
    public void ParserDistinguishesUnknownSchemeFromMalformedPayload()
    {
        var unknown = Assert.IsType<AnchorParseResult.Invalid>(
            Anchor.TryParseCanonical("unknown/value"));
        var malformed = Assert.IsType<AnchorParseResult.Invalid>(
            Anchor.TryParseCanonical("gict/v3.6/I.2/definitions/1.1-1.2"));

        Assert.NotEqual(unknown.Message, malformed.Message);
    }

    [Fact]
    public void ParsedAnchorsUseOrdinalValueEquality()
    {
        var first = Anchor.ParseCanonical("gict/v3.6/I.2/definition/1.4");
        var second = Anchor.ParseCanonical("gict/v3.6/I.2/definition/1.4");

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
            typeof(GictAnchor),
            typeof(PzgAnchor),
            typeof(SpecAnchor),
            typeof(LiteratureAnchor),
            typeof(MathlibAnchor),
        };

        Assert.All(subtypes, static type => Assert.Empty(type.GetConstructors()));
    }
}
