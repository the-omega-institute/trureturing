using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SymmetricHighGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric High Graph", H("Symmetric High Graph"),
        Blocks(
            Paragraph(Text("Form the actual graph induced by degree-three vertices, preserving full-graph incidences and deriving its degrees, bipartition and girth. It is a construction from the original graph, not an assumed high-graph classification.")),
            Paragraph(Text("This module contributes to the live proof path of SymmetricSliceExclusion.result. Private helper declarations are proof organization and carry no independent novelty claim."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyTwoLocal"))
        ]));
}
