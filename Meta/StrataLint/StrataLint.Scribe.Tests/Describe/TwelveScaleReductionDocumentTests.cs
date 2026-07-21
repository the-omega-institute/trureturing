namespace StrataLint.Scribe.Tests;

public sealed class TwelveScaleReductionDocumentTests
{
    [Fact]
    public void TwelveScaleReductionCarriesCanonicalExtractionAndTheConditionalFloorTheorem()
    {
        var definition = DocumentDefinitions.All.Single(static item =>
            item.Document.Header.Gid.Value == "D5/S1/Depth/TwelveScaleReduction");
        var describes = Descendants(definition.Document.Content)
            .OfType<DocumentBlock.Describe>()
            .ToArray();

        Assert.Equal(7, describes.Length);
        Assert.All(describes, static describe =>
        {
            Assert.Equal(DescribeKind.Theorem, describe.Kind);
            Assert.Equal(DescribeProvenanceKind.RepoDerived, describe.Provenance.Kind);
            var lean = Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement);
            Assert.True(lean.Value.RequireNoSorry);
        });
        Assert.Equal(
            [
                "D5/S1/Depth/TwelveScaleReduction.canonical_partial_quotients_empty_or_odd",
                "D5/S1/Depth/TwelveScaleReduction.canonical_continued_fraction_value",
                "D5/S1/Depth/TwelveScaleReduction.twelve_scale_le_normalized_magnitude",
                "D5/S1/Depth/TwelveScaleReduction.normalized_magnitude_eq_twelve_scale_iff",
                "D5/S1/Depth/TwelveScaleReduction.twelve_scale_is_normalized_sample_minimum",
                "D5/S1/Depth/TwelveScaleReduction.normalized_sample_minimum_unique",
                "D5/S1/Depth/TwelveScaleReduction.normalized_sample_floor_eq_twelve_over_maximum_partial_quotient",
            ],
            describes.Select(static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value));
        var floor = Assert.Single(describes, static describe =>
            describe.Id.Value == "continued-fraction-twelve-floor");
        Assert.NotNull(floor.StatementLatex);
        Assert.Contains(
            @"A(q)>0\land(\forall\psi\in S,\ 12\mid\psi\land\psi\neq0)",
            floor.StatementLatex.Value,
            StringComparison.Ordinal);
        Assert.Contains(
            @"\land(\exists\psi_0\in S,\ |\psi_0|=12)\Rightarrow\min",
            floor.StatementLatex.Value,
            StringComparison.Ordinal);
        Assert.Contains(
            @"A(q)=\max C(q)",
            floor.StatementLatex.Value,
            StringComparison.Ordinal);
        Assert.DoesNotContain(
            describes,
            static describe =>
                Assert.IsType<DescribeStatement.LeanDeclaration>(describe.Statement).Value.Value ==
                "D5/S1/Depth/TwelveScaleReduction.zero_family_lies_on_thirty_six_grid");

        var report = LeanReportFixture.ForDocuments([definition.Document]);
        var markdown = System.Text.Encoding.UTF8.GetString(
            CanonicalMarkdownWriter.Write(definition.Document, report).AsSpan());
        Assert.Contains(
            "does not supply the 2958-case or minimum-attainment certificates",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "does not identify the moat, envelope, or diffusion readings",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "does not reconstruct the historical sampling configuration or its leakage",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "derives the normalization denominator as the largest extracted partial quotient",
            markdown,
            StringComparison.Ordinal);
        Assert.Contains(
            "No independent scale parameter remains.",
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
