using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9PartnerGraphProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9PartnerGraphProbe", H("Q9PartnerGraphProbe"),
        Blocks(
            Paragraph(Text("A vertex at distance seven agrees with the root in two unused coordinate directions. These pairs form a graph on the six unused directions. The original Huang signing gives the even-degree restriction and determines the signed orientations."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeComponentBoundary")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9FourthLeafSignProbe"))
        ]));
}
