using System.Collections.Immutable;

namespace StrataLint.Definitions;

public static class ExternalAnchorManifest
{
    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        new AnchorDefinition(
            AnchorCatalogDefinitions.MathlibZeckendorfModule,
            "mathlib revision fabf563a7c95a166b8d7b6efca11c8b4dc9d911f; reference locator module Mathlib.Data.Nat.Fib.Zeckendorf"),
    ];
}
