using System.Reflection;

namespace StrataLint.ArchitectureTests;

public sealed class AnchorCatalogConsistencyTests
{
    [Fact]
    public void CatalogContainsOnlyExternalReferenceKinds()
    {
        Assert.All(AnchorCatalogDefinitions.All, static definition =>
            Assert.True(definition.Anchor is LiteratureAnchor or MathlibAnchor));
    }

    [Fact]
    public void CatalogDefinitionsAreExactlyTheExternalManifest()
    {
        Assert.Equal(
            ExternalAnchorManifest.All.ToArray(),
            AnchorCatalogDefinitions.All.ToArray());
    }

    [Fact]
    public void AnchorCatalogPropertyNamesMatchTheirCanonicalAnchors()
    {
        var properties = typeof(AnchorCatalogDefinitions)
            .GetProperties(BindingFlags.Static | BindingFlags.Public)
            .Where(static property => typeof(Anchor).IsAssignableFrom(property.PropertyType))
            .Select(static property => (
                property.Name,
                Anchor: Assert.IsAssignableFrom<Anchor>(property.GetValue(null))))
            .ToArray();

        Assert.Empty(FindPropertyNameMismatches(properties));
    }

    [Fact]
    public void MismatchedExternalAnchorPropertyNameIsRejectedByTheRedFixture()
    {
        var anchor = Anchor.ParseCanonical("mathlib/decl/Nat.zeckendorf");

        var mismatch = Assert.Single(FindPropertyNameMismatches(
            [(Name: "MathlibWrongDeclaration", Anchor: anchor)]));

        Assert.Equal("MathlibWrongDeclaration", mismatch.Actual);
        Assert.Equal("MathlibZeckendorfDeclaration", mismatch.Expected);
    }

    private static (string Actual, string Expected)[] FindPropertyNameMismatches(
        IEnumerable<(string Name, Anchor Anchor)> properties) =>
        properties
            .Select(static property => (
                Actual: property.Name,
                Expected: ExpectedPropertyName(property.Anchor)))
            .Where(static item => !string.Equals(
                item.Actual,
                item.Expected,
                StringComparison.Ordinal))
            .OrderBy(static item => item.Actual, StringComparer.Ordinal)
            .ToArray();

    private static string ExpectedPropertyName(Anchor anchor) => anchor switch
    {
        LiteratureAnchor literature => "Literature" + PascalBibKey(literature.BibKey.Value),
        MathlibAnchor mathlib => "Mathlib"
            + PascalIdentifier(mathlib.Name.Value.Split('.')[^1])
            + mathlib.TargetKind,
        _ => throw new InvalidOperationException(
            $"Catalog property-name transform is undefined for {anchor.Scheme}."),
    };

    private static string PascalBibKey(string value) =>
        PascalIdentifier(value);

    private static string PascalIdentifier(string value) =>
        char.ToUpperInvariant(value[0]) + value[1..];
}
