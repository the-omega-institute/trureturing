using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9FourthNeighborhoodProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9FourthNeighborhoodProbe", H("Q9FourthNeighborhoodProbe"),
        Blocks(
            Paragraph(Text("Count vertices reached in four steps by tracking their incidences with the third layer."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction"))
        ]));
}
