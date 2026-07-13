using System.Collections.Immutable;

namespace StrataLint.Scribe;

public static class ExternalAnchorManifest
{
    internal const string MathlibRevision = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f";

    public static ImmutableArray<AnchorDefinition> All { get; } =
    [
        new AnchorDefinition(
            AnchorCatalogDefinitions.MathlibZeckendorfModule,
            new MathlibSymbolTarget(
                "mathlib:module:Mathlib.Data.Nat.Fib.Zeckendorf",
                MathlibRevision,
                new StructuralSelector(
                    "module:Mathlib.Data.Nat.Fib.Zeckendorf",
                    "declaration:Nat.zeckendorf")),
            AnchorRegistrationStatus.RegisteredOpen,
            "D5-T0016",
            "external Lean environment receipt is not yet emitted by lean-inspector"),
    ];
}
