namespace StrataLint.ArchitectureTests;

public sealed class TheoryIsolationTests
{
    [Fact]
    public void RepositoryProgramAndFormalSourcesHaveNoInternalTheoryReferences()
    {
        var findings = TheoryIsolationPolicy.InspectRepository(RepositoryLayout.FindRoot());

        Assert.True(
            findings.Count == 0,
            string.Join(
                Environment.NewLine,
                findings.Select(static finding => $"{finding.Path}: {finding.Message}")));
    }

    [Fact]
    public void LeanHeaderTheorySchemeIsRejectedByTheRedFixture()
    {
        var retiredAnchor = string.Concat("gi", "ct/v9.0/I/theorem/1.0");
        var source = $$"""
            /- GID: D5/S0/Carrier/Synthetic
               generality: G
               mirror-B: none(waiver:synthetic)
               mirror-E: none(waiver:synthetic)
               anchors: [{{retiredAnchor}}]
               digest: Synthetic fixture. -/
            """;

        var finding = Assert.Single(TheoryIsolationPolicy.InspectSource(
            "D5/S0/Carrier/Synthetic.lean",
            source));

        Assert.Contains("internal theory reference", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CSharpNumberedTheoryCitationIsRejectedByTheRedFixture()
    {
        var retiredCitation = string.Concat("P", "ZG 26");
        var source = $$"""var citation = "{{retiredCitation}}";""";

        var finding = Assert.Single(TheoryIsolationPolicy.InspectSource(
            "Meta/StrataLint/StrataLint.Engine/Rules/Synthetic.cs",
            source));

        Assert.Contains("internal theory reference", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void CatalogTheorySchemeIsRejectedByTheRedFixture()
    {
        var retiredAnchor = string.Concat("pz", "g/v9/1.0");
        var catalog = $$"""
            {"definitions":[{"anchor":"{{retiredAnchor}}","provenance":"fixture"}],"schema_version":1}
            """;

        var finding = Assert.Single(TheoryIsolationPolicy.InspectCatalog(
            TheoryIsolationPolicy.AnchorCatalogPath,
            catalog));

        Assert.Contains("internal theory scheme", finding.Message, StringComparison.Ordinal);
    }

    [Fact]
    public void DigestionMachineIsTheOnlyCSharpException()
    {
        var sourcePath = string.Concat("docs/develop/", "theory/source.md");
        var sourceId = string.Concat("gi", "ct-v9");
        var source = $$"""
            var path = "{{sourcePath}}";
            var id = "{{sourceId}}";
            """;

        Assert.Empty(TheoryIsolationPolicy.InspectSource(
            "Meta/StrataLint/StrataLint.Engine/Digestion/Synthetic.cs",
            source));
    }
}
