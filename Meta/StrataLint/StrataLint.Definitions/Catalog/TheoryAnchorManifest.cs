using System.Collections.Immutable;

namespace StrataLint.Definitions;

public static class TheoryAnchorManifest
{
    internal static AnchorDefinition GictI1Definition1_1 { get; } = Gict(
        AnchorCatalogDefinitions.GictI1Definition1_1);

    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        GictI1Definition1_1,
        Gict(AnchorCatalogDefinitions.GictI1Definition1_2),
        Gict(AnchorCatalogDefinitions.GictI2Definition1_4),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3I),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3II),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3III),
        Gict(AnchorCatalogDefinitions.GictI1Theorem1_3IV),
        Gict(AnchorCatalogDefinitions.GictVII7Theorem7_15),
        Gict(AnchorCatalogDefinitions.GictVIIIHearts),
        Gict(AnchorCatalogDefinitions.GictAppendixA),
        Pzg(AnchorCatalogDefinitions.Pzg6_18),
        Pzg(AnchorCatalogDefinitions.Pzg6_19),
        Pzg(AnchorCatalogDefinitions.Pzg26_3),
        Pzg(AnchorCatalogDefinitions.Pzg26_4),
    ];

    private static AnchorDefinition Gict(GictAnchor anchor) =>
        new(anchor, $"GICT {anchor.Edition}; reference locator {anchor.ReferenceLocator}");

    private static AnchorDefinition Pzg(PzgAnchor anchor) =>
        new(anchor, $"PZG {anchor.Edition}; reference locator {anchor.ReferenceLocator}");
}
