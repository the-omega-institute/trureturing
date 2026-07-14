using System.Collections.Immutable;

namespace StrataLint.Definitions;

public static class AnchorCatalogDefinitions
{
    static AnchorCatalogDefinitions() { }

    public static MathlibAnchor MathlibZeckendorfModule { get; } =
        Require<MathlibAnchor>("mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf");

    private static readonly Lazy<ImmutableArray<AnchorDefinition>> AllDefinitions = new(() =>
        ExternalAnchorManifest.All
            .OrderBy(static item => item.Anchor.CanonicalString, StringComparer.Ordinal)
            .ToImmutableArray());

    public static ImmutableArray<AnchorDefinition> All => AllDefinitions.Value;

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
