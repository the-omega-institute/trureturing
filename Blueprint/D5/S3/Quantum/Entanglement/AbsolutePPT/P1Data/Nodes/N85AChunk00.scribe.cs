using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes;

internal sealed class N85AChunk00Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered literal node records 0 through 699; no acceptance result.",
        H("Exact P1 forest N85AChunk00"),
        Blocks(
            Describe.Lean(DescribeId.Create("nodes-chunk-0"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Nodes/N85AChunk00.nodes_chunk_0"),
                H("Ordered literal forest nodes_chunk_0"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The ordered records retain every box endpoint, rule, child index and rational coefficient. These data assert no successful check."))),
                DescribeRole.Definition))));
}
