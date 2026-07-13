using System.Collections.Immutable;

namespace StrataLint.Scribe;

public static class SpecAnchorManifest
{
    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        Spec(AnchorCatalogDefinitions.SpecA1, "A1"),
        Spec(AnchorCatalogDefinitions.SpecA11, "A11"),
        Spec(AnchorCatalogDefinitions.SpecSl002, "SL-002"),
        Spec(AnchorCatalogDefinitions.SpecSl003, "SL-003"),
        Spec(AnchorCatalogDefinitions.SpecSl014, "SL-014"),
        Spec(AnchorCatalogDefinitions.SpecSl016, "SL-016"),
        Spec(AnchorCatalogDefinitions.SpecSl017, "SL-017"),
        Spec(AnchorCatalogDefinitions.SpecSl018, "SL-018"),
        Spec(AnchorCatalogDefinitions.SpecSl019, "SL-019"),
        Spec(AnchorCatalogDefinitions.SpecByteCanonicalization, "byte-canonicalization"),
        Spec(AnchorCatalogDefinitions.SpecHumanGates, "human-gates"),
        Spec(AnchorCatalogDefinitions.SpecSample11, "sample-11"),
    ];

    private static AnchorDefinition Spec(
        SpecAnchor anchor,
        string locator) =>
        new(anchor, "golden-ledger spec v7.11; reference locator " + locator);
}
