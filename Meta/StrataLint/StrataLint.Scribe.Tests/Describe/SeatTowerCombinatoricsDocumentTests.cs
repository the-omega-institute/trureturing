namespace StrataLint.Scribe.Tests;

public sealed class SeatTowerCombinatoricsDocumentTests
{
    [Fact]
    public void SeatTowerCombinatoricsCarriesElevenTheoremsAndDisclosesItsModelBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Phase/SeatTowerCombinatorics");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(11, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
            Assert.True(lean.Value.RequireNoSorry);
        });
        Assert.Equal(
            [
                "D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity",
                "D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd",
                "D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count",
                "D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count",
                "D5/S1/Phase/SeatTowerCombinatorics.stationing_count",
                "D5/S1/Phase/SeatTowerCombinatorics.occupied_stations_mirror",
                "D5/S1/Phase/SeatTowerCombinatorics.mirror_occupied_count",
                "D5/S1/Phase/SeatTowerCombinatorics.mirror_stationing_ne_self",
                "D5/S1/Phase/SeatTowerCombinatorics.occupied_count_stationing_count",
                "D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique",
                "D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));

        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());
        Assert.Contains(
            "does not identify arithmetic orbits with stationings",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "No finite observation, measured exponent, density, or asymptotic law is closed",
            markdown,
            StringComparison.Ordinal);
    }

    private static IEnumerable<DocumentBlock> Descendants(BlockSequence content)
    {
        foreach (var block in content.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (nested is null) continue;
            foreach (var descendant in Descendants(nested)) yield return descendant;
        }
    }
}
