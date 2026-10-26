using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes;

internal sealed class N25AChunk02Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered literal node records 1400 through 2099; no acceptance result.",
        H("Exact P1 forest N25AChunk02"),
        Blocks(
            Describe.Lean(DescribeId.Create("nodes-chunk-1400"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Nodes/N25AChunk02.nodes_chunk_1400"),
                H("Ordered literal forest nodes_chunk_1400"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The ordered records retain every box endpoint, rule, child index and rational coefficient. These data assert no successful check."))),
                DescribeRole.Definition))));
}
