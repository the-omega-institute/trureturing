using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SixBoundarySideCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private helpers consumed by the actual six-boundary side-gap theorem.",
        H("Actual auxiliary edges and partners"),
        Blocks(Paragraph(Text("All helpers are private and consumed by SixBoundarySideGap. The auxiliary vertices are the actual degree-three right vertices. Ordinary left vertices with two high neighbors label core edges. Existing FifteenSliceStructure.core and its girth uniqueness helpers are reused. The code proves the exact neighbor bijection, triangle-freeness and degrees. Every ordinary left label has an actual degree-two right middle and a distinct left partner. Girth forbids shared high endpoints and cross edges between their high endpoint sets. The twelve case yields a cubic core with induced-disjoint partners; the eleven case yields one degree-two core vertex and cubic degrees elsewhere."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCounting")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/FifteenSliceStructure"))
        ]));
}
