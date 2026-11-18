using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical;

internal sealed class SixBoundarySideLabelingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Private helpers consumed by the actual six-boundary side-gap theorem.",
        H("Constructive local auxiliary graph analysis"),
        Blocks(Paragraph(Text("All helpers are private and consumed. The seven-vertex deficient-edge obstruction uses disjoint neighbor sets of size two inside a three-element set. The eight-vertex classification begins with an edge and its induced-disjoint partner and constructs all eight labels from actual third neighbors. Neighborhood unions partition the remaining four vertices. One mixed arrangement makes the required partner endpoints nonadjacent and is excluded. The surviving actual neighbor table is the cube. No list of arbitrary graphs, assumed normal form or graph-enumeration certificate supplies the classification. Vector and finite-index checks only establish injectivity and the explicit final labels."))),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/SixBoundarySideCore"))
        ]));
}
