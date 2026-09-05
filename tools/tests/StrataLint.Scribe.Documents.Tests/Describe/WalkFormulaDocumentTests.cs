namespace StrataLint.Scribe.Tests;

public sealed class WalkFormulaDocumentTests
{
    [Fact]
    public void WalkFormulaCarriesFourTheoremsAndDisclosesSemanticResiduals()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Phase/WalkFormula");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(4, describes.Length);
        Assert.All(describes, static describe =>
        {
            DocumentFactAssertions.RepoDerived(describe);
            DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem);
        });
        Assert.Equal(
            [
                "D5/S1/Phase/WalkFormula.alternating_walk_append",
                "D5/S1/Phase/WalkFormula.alternating_walk_reverse",
                "D5/S1/Phase/WalkFormula.endpoint_correction_is_integer",
                "D5/S1/Phase/WalkFormula.w3_walk_endpoint_translation",
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
