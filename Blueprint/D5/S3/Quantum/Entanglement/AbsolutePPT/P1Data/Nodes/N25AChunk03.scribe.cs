using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.P1Data.Nodes;

internal sealed class N25AChunk03Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered literal node records 2100 through 2440; no acceptance result.",
        H("Exact P1 forest N25AChunk03"),
        Blocks(
            Describe.Lean(DescribeId.Create("nodes-chunk-2100"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/P1Data/Nodes/N25AChunk03.nodes_chunk_2100"),
                H("Ordered literal forest nodes_chunk_2100"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The ordered records retain every box endpoint, rule, child index and rational coefficient. These data assert no successful check."))),
                DescribeRole.Definition))));
}
