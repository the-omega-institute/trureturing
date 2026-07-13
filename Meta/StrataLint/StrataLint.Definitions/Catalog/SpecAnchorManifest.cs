using System.Collections.Immutable;

namespace StrataLint.Definitions;

public static class SpecAnchorManifest
{
    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        Spec(AnchorCatalogDefinitions.SpecA1),
        Spec(AnchorCatalogDefinitions.SpecA11),
        Spec(AnchorCatalogDefinitions.SpecSl002),
        Spec(AnchorCatalogDefinitions.SpecSl003),
        Spec(AnchorCatalogDefinitions.SpecSl014),
        Spec(AnchorCatalogDefinitions.SpecSl016),
        Spec(AnchorCatalogDefinitions.SpecSl017),
        Spec(AnchorCatalogDefinitions.SpecSl018),
        Spec(AnchorCatalogDefinitions.SpecSl019),
        Spec(AnchorCatalogDefinitions.SpecByteCanonicalization),
        Spec(AnchorCatalogDefinitions.SpecHumanGates),
        Spec(AnchorCatalogDefinitions.SpecSample11),
    ];

    private static AnchorDefinition Spec(SpecAnchor anchor) =>
        new(
            anchor,
            $"golden-ledger spec {anchor.Edition}; reference locator {anchor.ReferenceLocator}");
}
