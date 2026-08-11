namespace StrataLint.ArchitectureTests;

public sealed class IndirectRepositoryReadInventoryTests
{
    private static readonly IReadOnlySet<string> PinnedBaseline = new HashSet<string>(StringComparer.Ordinal)
    {
        "Meta/StrataLint/StrataLint.Scribe.Tests/Describe/Quantum/ChannelFixedStateDocumentTests.cs:36",
        "Meta/StrataLint/StrataLint.Scribe.Tests/FileMap/FileMapManifestTests.cs:137",
        "Meta/StrataLint/StrataLint.Scribe.Tests/PdfWriterTests.cs:110",
        "Meta/StrataLint/StrataLint.Scribe.Tests/PilotDocumentTests.cs:519",
        "Meta/StrataLint/StrataLint.Scribe.Tests/Values/ValuesDefinitionTests.cs:49",
        "Meta/StrataLint/StrataLint.Scribe.Tests/Values/ValuesDefinitionTests.cs:84",
        "Meta/StrataLint/StrataLint.Scribe.Tests/Values/ValuesProjectionTests.cs:11",
        "Meta/StrataLint/StrataLint.Scribe.Tests/Values/ValuesProjectionTests.cs:28",
        "Meta/StrataLint/StrataLint.Scribe.Tests/Values/ValuesProjectionTests.cs:50",
    };

    [Fact]
    public void ExistingIndirectRepositoryReadsAreMachineInventoried()
    {
        var sites = ProductionRepositoryReadDeriver.InspectScribeTests(
            RepositoryLayout.FindRoot());

        Assert.True(
            sites.Count == 9,
            string.Join(Environment.NewLine, sites.Select(static site => site.Location)));
        Assert.Empty(ProductionRepositoryReadDeriver.FindAddedSites(
            sites.Select(static site => site.Location),
            PinnedBaseline));
    }

    [Fact]
    public void AddingIndirectRepositoryReadIsRejected()
    {
        var current = PinnedBaseline.Append("Meta/StrataLint/StrataLint.Scribe.Tests/NewTests.cs:10");

        Assert.Equal(
            ["Meta/StrataLint/StrataLint.Scribe.Tests/NewTests.cs:10"],
            ProductionRepositoryReadDeriver.FindAddedSites(current, PinnedBaseline));
    }

    [Fact]
    public void RemovingIndirectRepositoryReadIsAccepted()
    {
        var current = PinnedBaseline.Skip(1);

        Assert.Empty(ProductionRepositoryReadDeriver.FindAddedSites(current, PinnedBaseline));
    }
}
