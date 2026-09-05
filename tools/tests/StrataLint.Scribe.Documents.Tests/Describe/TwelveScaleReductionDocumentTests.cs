namespace StrataLint.Scribe.Tests;

public sealed class TwelveScaleReductionDocumentTests
{
    [Fact]
    public void TwelveScaleReductionCarriesFourPartialTheoremsAndRetainsSourceResiduals()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Depth/TwelveScaleReduction");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(4, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });
        Assert.Equal(
            [
                "D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude",
                "D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff",
                "D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum",
                "D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));
        Assert.DoesNotContain(
            describes,
            static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value ==
                "D5/S1/Depth/TwelveScaleReduction.zero_family_lies_on_thirty_six_grid");

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
