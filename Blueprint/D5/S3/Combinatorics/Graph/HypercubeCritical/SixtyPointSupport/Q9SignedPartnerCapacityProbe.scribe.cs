using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.SixtyPointSupport;

internal sealed class Q9SignedPartnerCapacityProbeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Q9SignedPartnerCapacityProbe", H("Q9SignedPartnerCapacityProbe"),
        Blocks(
            Paragraph(Text("Compare the signs imposed on each rank-three label by its incident rank-two partners. The resulting incidence bound charges each selected triangle and each degree-two coordinate in the partner graph."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixtyPointSupport/Q9PartnerGraphProbe"))
        ]));
}
