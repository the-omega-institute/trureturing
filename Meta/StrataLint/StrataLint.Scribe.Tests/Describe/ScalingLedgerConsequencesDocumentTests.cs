namespace StrataLint.Scribe.Tests;

public sealed class ScalingLedgerConsequencesDocumentTests
{
    [Fact]
    public void ScalingLedgerConsequencesCarriesThreeExactTheoremsAndRetainsGovernanceBoundary()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S3/Zeros/ScalingLedgerConsequences");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(3, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
            Assert.True(lean.Value.RequireNoSorry);
        });
        Assert.Equal(
            [
                "D5/S3/Zeros/ScalingLedgerConsequences.half_density_phase_scaling_factorization",
                "D5/S3/Zeros/ScalingLedgerConsequences.scaling_ledger_unbounded_on_multiples",
                "D5/S3/Zeros/ScalingLedgerConsequences.unit_rotation_preserves_coefficient_norm",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));

        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());
        Assert.Contains("all three mathematical clauses of the coordinatewise scaling definition",
            markdown, StringComparison.Ordinal);
        Assert.Contains("does not authorize an address-dependent inverse scaling register",
            markdown, StringComparison.Ordinal);
        Assert.Contains("does not assert a statement about an analytically continued sum",
            markdown, StringComparison.Ordinal);
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
