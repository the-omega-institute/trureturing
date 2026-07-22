namespace StrataLint.Scribe.Tests;

public sealed class WindowParityDocumentTests
{
    [Fact]
    public void WindowParityCarriesTwoExactTheoremsAndRetainsInterpretiveResiduals()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Depth/WindowParity");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(2, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
            Assert.True(lean.Value.RequireNoSorry);
        });
        Assert.Equal(
            [
                "D5/S1/Depth/WindowParity.full_window_and_golden_capacity",
                "D5/S1/Depth/WindowParity.witt_window_sum_parity",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));

        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());
        Assert.Contains("cascade chirality remains unresolved", markdown, StringComparison.Ordinal);
        Assert.Contains("No empirical certificate or asymptotic claim follows", markdown,
            StringComparison.Ordinal);
        Assert.Contains("the exact integer floor of the cubed golden ratio", markdown,
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
