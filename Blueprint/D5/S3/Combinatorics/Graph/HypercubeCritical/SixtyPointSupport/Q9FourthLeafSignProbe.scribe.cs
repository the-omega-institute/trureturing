using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9FourthLeafSignProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9FourthLeafSignProbe", H("Q9FourthLeafSignProbe"),
        Blocks(
            Paragraph(Text("Huang balance fixes the order of the middle directions of a four-step walk when the first and last directions coincide."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9FourthNeighborhoodProbe"))
        ]));
}
