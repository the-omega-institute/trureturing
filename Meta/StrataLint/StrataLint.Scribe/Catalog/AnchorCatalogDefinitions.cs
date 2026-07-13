using System.Collections.Immutable;

namespace StrataLint.Scribe;

public static class AnchorCatalogDefinitions
{
    static AnchorCatalogDefinitions() { }

    public static GictAnchor GictI1Definition1_1 { get; } =
        Require<GictAnchor>("gict/v3.6/I.1/definition/1.1");

    public static GictAnchor GictI1Definition1_2 { get; } =
        Require<GictAnchor>("gict/v3.6/I.1/definition/1.2");

    public static GictAnchor GictI2Definition1_4 { get; } =
        Require<GictAnchor>("gict/v3.6/I.2/definition/1.4");

    public static GictAnchor GictI1Theorem1_3I { get; } =
        Require<GictAnchor>("gict/v3.6/I.1/theorem/1.3/i");

    public static GictAnchor GictI1Theorem1_3II { get; } =
        Require<GictAnchor>("gict/v3.6/I.1/theorem/1.3/ii");

    public static GictAnchor GictI1Theorem1_3III { get; } =
        Require<GictAnchor>("gict/v3.6/I.1/theorem/1.3/iii");

    public static GictAnchor GictI1Theorem1_3IV { get; } =
        Require<GictAnchor>("gict/v3.6/I.1/theorem/1.3/iv");

    public static GictAnchor GictVII7Theorem7_15 { get; } =
        Require<GictAnchor>("gict/v3.6/VII.7/theorem/7.15");

    public static GictAnchor GictVIIIHearts { get; } =
        Require<GictAnchor>("gict/v3.6/VIII/section/hearts");

    public static GictAnchor GictAppendixA { get; } =
        Require<GictAnchor>("gict/v3.6/appendix/A");

    public static PzgAnchor Pzg6_18 { get; } = Require<PzgAnchor>("pzg/v170/6.18");

    public static PzgAnchor Pzg6_19 { get; } = Require<PzgAnchor>("pzg/v170/6.19");

    public static PzgAnchor Pzg26_3 { get; } = Require<PzgAnchor>("pzg/v170/26.3");

    public static PzgAnchor Pzg26_4 { get; } = Require<PzgAnchor>("pzg/v170/26.4");

    public static SpecAnchor SpecA1 { get; } = Require<SpecAnchor>("spec/v7.11/A1");

    public static SpecAnchor SpecA11 { get; } = Require<SpecAnchor>("spec/v7.11/A11");

    public static SpecAnchor SpecSl002 { get; } = Require<SpecAnchor>("spec/v7.11/SL-002");

    public static SpecAnchor SpecSl003 { get; } = Require<SpecAnchor>("spec/v7.11/SL-003");

    public static SpecAnchor SpecSl014 { get; } = Require<SpecAnchor>("spec/v7.11/SL-014");

    public static SpecAnchor SpecSl016 { get; } = Require<SpecAnchor>("spec/v7.11/SL-016");

    public static SpecAnchor SpecSl017 { get; } = Require<SpecAnchor>("spec/v7.11/SL-017");

    public static SpecAnchor SpecSl018 { get; } = Require<SpecAnchor>("spec/v7.11/SL-018");

    public static SpecAnchor SpecSl019 { get; } = Require<SpecAnchor>("spec/v7.11/SL-019");

    public static SpecAnchor SpecByteCanonicalization { get; } =
        Require<SpecAnchor>("spec/v7.11/byte-canonicalization");

    public static SpecAnchor SpecHumanGates { get; } =
        Require<SpecAnchor>("spec/v7.11/human-gates");

    public static SpecAnchor SpecSample11 { get; } =
        Require<SpecAnchor>("spec/v7.11/sample-11");

    public static MathlibAnchor MathlibZeckendorfModule { get; } =
        Require<MathlibAnchor>("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");

    private static readonly Lazy<ImmutableArray<AnchorDefinition>> AllDefinitions = new(() =>
        TheoryAnchorManifest.All
            .AddRange(SpecAnchorManifest.All)
            .AddRange(ExternalAnchorManifest.All)
            .OrderBy(static item => item.Anchor.CanonicalString, StringComparer.Ordinal)
            .ToImmutableArray());

    public static ImmutableArray<AnchorDefinition> All => AllDefinitions.Value;

    public static AnchorDefinition GictI1Definition1_1Definition =>
        TheoryAnchorManifest.GictI1Definition1_1;

    internal static bool TryGet(string canonical, out AnchorDefinition? definition)
    {
        definition = All.FirstOrDefault(item =>
            string.Equals(item.Anchor.CanonicalString, canonical, StringComparison.Ordinal));
        return definition is not null;
    }

    private static T Require<T>(string value)
        where T : Anchor =>
        Anchor.ParseCanonical(value) is T anchor
            ? anchor
            : throw new InvalidOperationException($"Catalog anchor {value} has the wrong subtype.");
}
