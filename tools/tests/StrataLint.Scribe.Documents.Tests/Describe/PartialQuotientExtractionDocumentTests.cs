namespace StrataLint.Scribe.Tests;

public sealed class PartialQuotientExtractionDocumentTests
{
    [Fact]
    public void PartialQuotientExtractionCarriesTheEndogenousFloorContract()
    {
        var definition = DocumentAssembly.Definitions.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Depth/PartialQuotientExtraction");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(5, describes.Length);
        Assert.All(describes, DocumentFactAssertions.RepoDerived);
        Assert.Equal(
            [
                "D5/S1/Depth/PartialQuotientExtraction.partialQuotients",
                "D5/S1/Depth/PartialQuotientExtraction.aMax",
                "D5/S1/Depth/PartialQuotientExtraction.partialQuotients_nonempty",
                "D5/S1/Depth/PartialQuotientExtraction.aMax_pos",
                "D5/S1/Depth/PartialQuotientExtraction.twelve_scale_is_extracted_normalized_sample_minimum",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));
        Assert.Equal(
            [
                DescribeKind.Definition,
                DescribeKind.Definition,
                DescribeKind.Theorem,
                DescribeKind.Theorem,
                DescribeKind.Theorem,
            ],
            describes.Select(static describe => describe.Kind));
        Assert.Collection(
            describes,
            describe => DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Definition),
            describe => DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Definition),
            describe => DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem),
            describe => DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem),
            describe => DocumentFactAssertions.Declaration(describe, LeanDeclarationKind.Theorem));

        var floor = Assert.Single(describes, static describe =>
            describe.Id.Value == "continued-fraction-twelve-floor");
        var layout = Assert.IsType<Formula.Layout>(floor.StatementFormula);
        Assert.IsType<Formula.LatexSequence>(layout.Content);
        Assert.Equal(
            "$$\\forall q\\in\\mathbb{Q}\\setminus\\mathbb{Z},\\ \\forall S\\subset_{\\mathrm{fin}}\\mathbb{Z},\\ (\\forall\\psi\\in S,\\ 12\\mid\\psi\\land\\psi\\neq0)\\land(\\exists\\psi_0\\in S,\\ |\\psi_0|=12)\\Rightarrow\\min\\left\\{\\frac{|\\psi|}{A(q)}:\\psi\\in S\\right\\}=\\frac{12}{A(q)},\\qquad A(q)=\\max C(q)$$",
            LatexWriter.WriteStatement(layout));

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
