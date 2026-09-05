namespace StrataLint.Scribe.Tests;

public sealed class ProvenanceAcknowledgementTests
{
    private const string NoteGid = "D5/L/Quantum/sample1987paper";

    [Fact]
    public void LandauCommutingCollapseUsesTypedAcknowledgementWithoutInlineGidCopy()
    {
        var document = Assert.Single(
            DocumentAssembly.Definitions,
            static item => item.Document.Header.Gid.Value
                == "D5/S3/QuantumBounds/LandauCommutingCollapse").Document;
        var describe = Assert.Single(document.Content.Items.OfType<DocumentBlock.Describe>());
        var provenance = Assert.IsType<AssessedProvenance.RepoDerived>(describe.AssessedProvenance);
        var inlineReferences = EnumerateBlocks(describe.Content)
            .OfType<DocumentBlock.Paragraph>()
            .SelectMany(static paragraph => paragraph.Content.Items)
            .OfType<Inline.GidReference>()
            .Select(static reference => reference.Reference.Value);

        Assert.Equal([NoteGid.Replace("sample1987paper", "landau1987violation")],
            provenance.Acknowledgements.Select(static item => item.Value));
        Assert.DoesNotContain(
            "D5/L/Quantum/landau1987violation",
            inlineReferences,
            StringComparer.Ordinal);
    }

    private static IEnumerable<DocumentBlock> EnumerateBlocks(BlockSequence blocks)
    {
        foreach (var block in blocks.Items)
        {
            yield return block;
            var nested = block switch
            {
                DocumentBlock.Section section => section.Content,
                DocumentBlock.Describe describe => describe.Content,
                _ => null,
            };
            if (nested is null) continue;
            foreach (var descendant in EnumerateBlocks(nested)) yield return descendant;
        }
    }
}
