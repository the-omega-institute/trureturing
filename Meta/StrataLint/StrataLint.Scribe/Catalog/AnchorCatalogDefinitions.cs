using System.Collections.Immutable;

namespace StrataLint.Scribe;

public static class AnchorCatalogDefinitions
{
    static AnchorCatalogDefinitions() { }

    private static readonly Lazy<ImmutableArray<AnchorDefinition>> AllDefinitions = new(() =>
        ExternalAnchorManifest.All
            .OrderBy(static item => item.Anchor.CanonicalString, StringComparer.Ordinal)
            .ToImmutableArray());

    public static MathlibAnchor MathlibZeckendorfModule { get; } =
        Require<MathlibAnchor>(nameof(MathlibZeckendorfModule));

    public static ImmutableArray<AnchorDefinition> All => AllDefinitions.Value;

    internal static bool TryGet(string canonical, out AnchorDefinition? definition)
    {
        definition = All.FirstOrDefault(item =>
            string.Equals(item.Anchor.CanonicalString, canonical, StringComparison.Ordinal));
        return definition is not null;
    }

    private static T Require<T>(string name)
        where T : Anchor =>
        All.SingleOrDefault(definition => string.Equals(definition.Name, name, StringComparison.Ordinal))
            ?.Anchor is T anchor
            ? anchor
            : throw new InvalidOperationException($"Catalog anchor {name} is missing or has the wrong subtype.");
}
