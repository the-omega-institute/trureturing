namespace StrataLint.Scribe.Tests;

public sealed class PartialQuotientExtractionDocumentTests
{
    [Fact]
    public void PartialQuotientExtractionCarriesTheEndogenousFloorContract()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Depth/PartialQuotientExtraction");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(5, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
            Assert.True(lean.Value.RequireNoSorry);
        });
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

        var floor = Assert.Single(describes, static describe =>
            describe.Id.Value == "continued-fraction-twelve-floor");
        Assert.NotNull(floor.StatementLatex);
        Assert.Contains(@"A(q)=\max C(q)", floor.StatementLatex.Value, StringComparison.Ordinal);
        Assert.Contains(
            @"(\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)",
            floor.StatementLatex.Value,
            StringComparison.Ordinal);
        Assert.Contains(
            @"(\exists\psi_0\in S,\ |\psi_0|=12)",
            floor.StatementLatex.Value,
            StringComparison.Ordinal);

        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());
        Assert.Contains("computed from the rational input itself", markdown, StringComparison.Ordinal);
        Assert.Contains("No independent scale parameter remains", markdown, StringComparison.Ordinal);
        Assert.Contains("sample-to-rational provenance remains open", markdown, StringComparison.Ordinal);
        Assert.Contains("moat, envelope, and diffusion residuals remain open", markdown, StringComparison.Ordinal);
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
