using System.Collections.Immutable;

namespace StrataLint.Scribe;

public static class TheoryAnchorManifest
{
    internal static AnchorDefinition GictI1Definition1_1 { get; } = Gict(
        AnchorCatalogDefinitions.GictI1Definition1_1,
        "I.1 definition 1.1");

    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        GictI1Definition1_1,
        Gict(AnchorCatalogDefinitions.GictI1Definition1_2, "I.1 definition 1.2"),
        Gict(AnchorCatalogDefinitions.GictI2Definition1_4, "I.2 definition 1.4"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3I, "I.1 theorem 1.3 i"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3II, "I.1 theorem 1.3 ii"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3III, "I.1 theorem 1.3 iii"),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3IV, "I.1 theorem 1.3 iv"),
        Gict(AnchorCatalogDefinitions.GictVII7Theorem7_15, "VII.7 theorem 7.15"),
        Gict(AnchorCatalogDefinitions.GictVIIIHearts, "VIII section hearts"),
        Gict(AnchorCatalogDefinitions.GictAppendixA, "appendix A"),
        Pzg(AnchorCatalogDefinitions.Pzg6_18, "6.18"),
        Pzg(AnchorCatalogDefinitions.Pzg6_19, "6.19"),
        Pzg(AnchorCatalogDefinitions.Pzg26_3, "26.3"),
        Pzg(AnchorCatalogDefinitions.Pzg26_4, "26.4"),
    ];

    private static AnchorDefinition Gict(
        GictAnchor anchor,
        string locator) =>
        new(anchor, "GICT v3.6; reference locator " + locator);

    private static AnchorDefinition Pzg(
        PzgAnchor anchor,
        string locator) =>
        new(anchor, "PZG v170; reference locator " + locator);
}
