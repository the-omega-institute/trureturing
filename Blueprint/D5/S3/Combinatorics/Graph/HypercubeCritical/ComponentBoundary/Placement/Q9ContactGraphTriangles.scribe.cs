using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9ContactGraphTrianglesDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent cubic vertices in the distance-two contact graph have either zero or two common neighbors.",
        H("Common neighbors at a cubic contact edge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-edge-common-neighbor-has-companion"),
                DeclarationHandle.Create(Placement + "Q9ContactGraphTriangles.cubic_edge_common_neighbor_has_companion"),
                H("A common neighbor of a cubic contact edge has a companion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An edge whose endpoints both have degree three has two remaining neighbors at each endpoint. If the endpoints share one of these neighbors, the two remaining neighbor sets must coincide. This constraint applies regardless of the shared neighbor's degree and is preserved by coordinate relabeling."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9CubicContactCommonPartner"))]));
}
