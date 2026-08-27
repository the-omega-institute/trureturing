namespace StrataLint.Scribe.Tests;

public sealed class KatexParserTests
{
    [Fact]
    public void ParsesWithThePinnedVendoredKatex()
    {
        var parser = KatexParser.Create();

        // The version is pinned by the vendored bytes; tools/vendor/katex/README.md
        // records where they came from, and raising it is a deliberate act.
        Assert.Equal("0.16.22", parser.Version);
        Assert.Null(parser.Reject(@"\sum_{n=0}^{\infty} {T^{*}}^{n} C^{*} C T^{n}", displayMode: true));
        Assert.Null(parser.Reject(@"\frac12 < \Re\left(s\right)", displayMode: false));
    }

    [Fact]
    public void RejectsTheShapesThatReachedTheSiteUnrendered()
    {
        var parser = KatexParser.Create();

        Assert.Contains(
            "Double superscript",
            parser.Reject(@"\beta^{n} T^{*}^{n}", displayMode: true),
            StringComparison.Ordinal);
        Assert.Contains(
            "Double subscript",
            parser.Reject("N < u_{n}_{i}", displayMode: true),
            StringComparison.Ordinal);
        Assert.Contains(
            "Expected group as argument",
            parser.Reject(@"\operatorname\left({NeZero}, d\right)", displayMode: true),
            StringComparison.Ordinal);
    }

    [Fact]
    public void KeepsRenderableButUnidiomaticInputGreen()
    {
        // The corpus emits `\\{}` line breaks in display mode by the thousand. KaTeX's
        // strict mode warns about them; the site renders them, so the gate must not
        // manufacture a verdict the site does not act on.
        var parser = KatexParser.Create();

        Assert.Null(parser.Reject(@"a = b,\\{}c = d", displayMode: true));
    }

    [Fact]
    public void CarriesTheVendoredBundleInTheAssemblyThatRunsIt()
    {
        // Embedded rather than read from the tree: the parser is a program the harness
        // executes, and nothing about judging a formula should depend on a file path.
        using var bundle = typeof(KatexParser).Assembly
            .GetManifestResourceStream(KatexParser.ResourceName);

        Assert.NotNull(bundle);
        Assert.True(bundle.Length > 100_000);
    }
}
