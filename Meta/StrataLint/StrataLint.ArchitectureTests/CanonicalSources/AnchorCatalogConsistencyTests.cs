using System.Reflection;
using Microsoft.CodeAnalysis;
using Microsoft.CodeAnalysis.CSharp;
using Microsoft.CodeAnalysis.CSharp.Syntax;
using StrataLint.Engine;
using StrataLint.Scribe;

namespace StrataLint.ArchitectureTests;

public sealed class AnchorCatalogConsistencyTests
{
    private const string TheoryManifestPath =
        "Meta/StrataLint/StrataLint.Definitions/Catalog/TheoryAnchorManifest.cs";
    private const string SpecManifestPath =
        "Meta/StrataLint/StrataLint.Definitions/Catalog/SpecAnchorManifest.cs";

    [Fact]
    public void AnchorManifestFactoriesDoNotAcceptHandwrittenLocators()
    {
        var offenders = new[] { typeof(TheoryAnchorManifest), typeof(SpecAnchorManifest) }
            .SelectMany(static type => type.GetMethods(
                BindingFlags.Static | BindingFlags.NonPublic | BindingFlags.DeclaredOnly))
            .Where(static method => method.ReturnType == typeof(AnchorDefinition))
            .Where(static method => method.GetParameters().Any(
                static parameter => parameter.ParameterType == typeof(string)))
            .Select(static method => $"{method.DeclaringType!.Name}.{method.Name}")
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.True(
            offenders.Length == 0,
            "anchor manifest factories accept handwritten locator strings: "
            + string.Join(", ", offenders));
    }

    [Fact]
    public void TheoryAndSpecManifestLocatorsAreDerivedFromCanonicalAnchors()
    {
        var mismatches = TheoryAnchorManifest.All
            .AddRange(SpecAnchorManifest.All)
            .Select(static definition =>
                (Definition: definition, Locator: ProvenanceLocator(definition.Provenance)))
            .Where(static item => !string.Equals(
                item.Locator,
                ReferenceLocator(item.Definition.Anchor),
                StringComparison.Ordinal))
            .Select(static item => item.Definition.Anchor.CanonicalString)
            .ToArray();

        Assert.Empty(mismatches);
    }

    [Fact]
    public void AnchorManifestsContainNoHandwrittenCanonicalLocatorLiterals()
    {
        var repositoryRoot = RepositoryLayout.FindRoot();
        var locators = TheoryAnchorManifest.All
            .AddRange(SpecAnchorManifest.All)
            .Select(static definition => ReferenceLocator(definition.Anchor))
            .ToHashSet(StringComparer.Ordinal);
        var findings = new[] { TheoryManifestPath, SpecManifestPath }
            .SelectMany(path => FindHandwrittenLocatorLiterals(
                File.ReadAllText(Path.Combine(repositoryRoot, path)),
                locators)
                .Select(locator => $"{path}: {locator}"))
            .ToArray();

        Assert.Empty(findings);
    }

    [Theory]
    [InlineData("\"I.2 definition 1.4\"", "I.2 definition 1.4")]
    [InlineData(
        "\"golden-ledger spec v7.11; reference locator SL-002\"",
        "SL-002")]
    public void HandwrittenCanonicalLocatorLiteralIsRejectedByTheRedFixture(
        string source,
        string locator)
    {
        var finding = Assert.Single(FindHandwrittenLocatorLiterals(
            source,
            new HashSet<string>(StringComparer.Ordinal) { locator }));

        Assert.Equal(source.Trim('"'), finding);
    }

    [Fact]
    public void SpecRuleAnchorsAreKnownRuleCatalogMembers()
    {
        var knownRuleIds = RuleCatalog.Default.Descriptors
            .Select(static descriptor => descriptor.Id.Value)
            .ToHashSet(StringComparer.Ordinal);
        var unknown = FindUnknownSpecRuleIds(
            SpecAnchorManifest.All.Select(static definition => definition.Anchor),
            knownRuleIds);

        Assert.Empty(unknown);
    }

    [Fact]
    public void UnknownSpecRuleAnchorIsRejectedByTheRedFixture()
    {
        var anchor = Anchor.ParseCanonical("spec/v7.11/SL-999");

        var unknown = FindUnknownSpecRuleIds(
            [anchor],
            new HashSet<string>(StringComparer.Ordinal) { "SL-001" });

        Assert.Equal(["SL-999"], unknown);
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
    public void MismatchedAnchorPropertyNameIsRejectedByTheRedFixture()
    {
        var anchor = Anchor.ParseCanonical("spec/v7.11/SL-002");

        var mismatch = Assert.Single(FindPropertyNameMismatches(
            [(Name: "SpecSl999", Anchor: anchor)]));

        Assert.Equal("SpecSl999", mismatch.Actual);
        Assert.Equal("SpecSl002", mismatch.Expected);
    }

    private static string ProvenanceLocator(string provenance)
    {
        const string marker = "reference locator ";
        var index = provenance.IndexOf(marker, StringComparison.Ordinal);
        Assert.True(index >= 0, $"provenance has no reference locator: {provenance}");
        return provenance[(index + marker.Length)..];
    }

    private static string ReferenceLocator(Anchor anchor) =>
        string.Join(' ', anchor.CanonicalString.Split('/').Skip(2));

    private static string[] FindHandwrittenLocatorLiterals(
        string source,
        IReadOnlySet<string> canonicalLocators) =>
        CSharpSyntaxTree.ParseText(source)
            .GetRoot()
            .DescendantNodes()
            .OfType<LiteralExpressionSyntax>()
            .Where(static literal => literal.IsKind(Microsoft.CodeAnalysis.CSharp.SyntaxKind.StringLiteralExpression))
            .Select(static literal => literal.Token.ValueText)
            .Where(value => canonicalLocators.Any(locator =>
                string.Equals(value, locator, StringComparison.Ordinal)
                || value.EndsWith("reference locator " + locator, StringComparison.Ordinal)))
            .ToArray();

    private static string[] FindUnknownSpecRuleIds(
        IEnumerable<Anchor> anchors,
        IReadOnlySet<string> knownRuleIds) =>
        anchors
            .OfType<SpecAnchor>()
            .Select(static anchor => anchor.Clause.Value)
            .Where(IsRuleClause)
            .Where(clause => !knownRuleIds.Contains(clause))
            .Order(StringComparer.Ordinal)
            .ToArray();

    private static bool IsRuleClause(string clause) =>
        clause.Length == 6
        && clause.StartsWith("SL-", StringComparison.Ordinal)
        && clause.AsSpan(3).IndexOfAnyExceptInRange('0', '9') < 0;

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
        GictAnchor gict => GictPropertyName(gict),
        PzgAnchor pzg => "Pzg" + pzg.Entry.ToString().Replace('.', '_'),
        SpecAnchor spec => "Spec" + PascalSlug(spec.Clause.Value),
        MathlibAnchor mathlib => "Mathlib"
            + mathlib.Name.Value.Split('.')[^1]
            + mathlib.TargetKind,
        _ => throw new InvalidOperationException(
            $"Catalog property-name transform is undefined for {anchor.Scheme}."),
    };

    private static string GictPropertyName(GictAnchor anchor)
    {
        if (anchor.Kind is TheoryNodeKind.Appendix)
        {
            return "GictAppendix" + anchor.Label.Value;
        }

        var kind = anchor.Kind is TheoryNodeKind.Section ? string.Empty : anchor.Kind.ToString();
        var label = anchor.Kind is TheoryNodeKind.Section
            ? PascalSlug(anchor.Label.Value)
            : anchor.Label.Value.Replace('.', '_');
        var subclaim = anchor.Subclaim?.Value.ToUpperInvariant() ?? string.Empty;
        return "Gict"
            + anchor.Division!.Value.Replace(".", string.Empty, StringComparison.Ordinal)
            + kind
            + label
            + subclaim;
    }

    private static string PascalSlug(string value) => string.Concat(
        value.Split('-', StringSplitOptions.RemoveEmptyEntries)
            .Select(static segment => char.ToUpperInvariant(segment[0])
                + segment[1..].ToLowerInvariant()));
}
