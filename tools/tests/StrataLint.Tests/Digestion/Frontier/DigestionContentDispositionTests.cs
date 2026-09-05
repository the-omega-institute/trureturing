using StrataLint.Engine;

namespace StrataLint.Tests;

public sealed class DigestionContentDispositionTests
{
    private static readonly string[] FormalizableAliases =
        ["theorem", "proposition", "lemma", "corollary", "theorem-form", "定理", "命题", "引理", "推论", "候签定理"];

    [Fact]
    public void EveryEnumeratedAtomizerKindHasExactlyOneDisposition()
    {
        var kinds = TheoryAtomizerRules.AllowedKinds
            .Concat(FormalizableAliases)
            .Concat(["none", "unregistered:未登记体"])
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();

        foreach (var kind in kinds)
        {
            var disposition = DigestionContentDisposition.Resolve(kind);

            Assert.Equal(kind, disposition.KindLabel);
            Assert.Equal(
                FormalizableAliases.Contains(kind, StringComparer.Ordinal)
                    ? DigestionContentRole.FormalizableClaim
                    : DigestionContentRole.NotFormalizable,
                disposition.Role);
        }

        Assert.Equal(
            (DigestionContentRole.NotFormalizable, "none"),
            DigestionContentDisposition.Resolve(null));
    }

    [Fact]
    public void DispositionKindUniverseEqualsTheAtomizerDerivedUnion()
    {
        var rules = DigestionTestSupport.Rules;
        var configuredLocators = rules.ObserverClaimPrefixes
            .Concat(rules.ConeClaimPrefixes)
            .Concat(rules.GictClaimPrefixes)
            .Concat(rules.GictConstants)
            .Concat(rules.PzgHeadingPrefixes)
            .SelectMany(static mapping => mapping.Value.Split('|'));
        var registeredGenres = rules.GictGenres
            .Concat(rules.PzgGenres)
            .Concat(rules.Dialects.Values.SelectMany(static dialect =>
                dialect.Genres.Concat(dialect.GenreSuffixes)))
            .Select(static mapping => mapping.Value);
        var builtInLocatorKinds = new[]
        {
            GenericAtomizer.ItemKind,
            GenericAtomizer.RowKind,
            GenericAtomizer.SectionKind,
            GictAtomizer.AppendixKind,
            PeriodicTreeAtomizer.CoarseKind,
            PeriodicTreeAtomizer.SectionKind,
            PzgAtomizer.MetadataKind,
            PzgAtomizer.OpenKind,
            PzgAtomizer.RemarkKind,
            PzgAtomizer.TraceNoteKind,
            WmAtomizer.AuditKind,
            WmAtomizer.MetadataKind,
            WmAtomizer.SectionKind,
            WmAtomizer.VersionKind,
        };
        var atomizerDerived = TheoryAtomizerRules.AllowedKinds
            .Concat(configuredLocators)
            .Concat(registeredGenres)
            .Concat(builtInLocatorKinds)
            .Select(ContentKind)
            .Distinct(StringComparer.Ordinal)
            .Order(StringComparer.Ordinal)
            .ToArray();

        Assert.Equal(
            atomizerDerived.Concat(FormalizableAliases)
                .Append("none")
                .Distinct(StringComparer.Ordinal)
                .Order(StringComparer.Ordinal),
            DigestionContentDisposition.KnownKindLabels);
    }

    [Fact]
    public void UnknownContentKindThrowsNamedFormatException()
    {
        var error = Assert.Throws<FormatException>(() =>
            DigestionContentDisposition.Resolve("developer-introduced-kind"));

        Assert.Equal("content kind 'developer-introduced-kind' has no disposition", error.Message);
    }

    private static string ContentKind(string locator)
    {
        var separator = locator.IndexOf('/', StringComparison.Ordinal);
        return separator < 0 ? locator : locator[..separator];
    }

}
