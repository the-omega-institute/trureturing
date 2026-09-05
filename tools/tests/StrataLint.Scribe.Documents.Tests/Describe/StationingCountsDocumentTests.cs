namespace StrataLint.Scribe.Tests;

public sealed class StationingCountsDocumentTests
{
    [Fact]
    public void StationingCountsCarriesFiveTheoremsAndDisclosesItsModelBoundary()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Depth/StationingCombinatorics");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(5, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });
        Assert.Equal(
            [
                "D5/S1/Depth/StationingCombinatorics.stationing_count",
                "D5/S1/Depth/StationingCombinatorics.occupied_stations_mirror",
                "D5/S1/Depth/StationingCombinatorics.mirror_occupied_count",
                "D5/S1/Depth/StationingCombinatorics.mirror_stationing_ne_self",
                "D5/S1/Depth/StationingCombinatorics.occupied_count_stationing_count",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));

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
