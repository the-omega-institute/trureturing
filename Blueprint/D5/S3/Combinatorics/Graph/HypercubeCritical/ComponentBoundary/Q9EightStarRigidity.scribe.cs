using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9EightStarRigidityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9EightStarRigidity";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eight-column rigidity of the occupied graph",
        H("Eight-column rigidity of the occupied graph"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("occupied-triangles-edge-cap"),
                DeclarationHandle.Create(Module + ".occupied_edge_triangle_unique"),
                H("Occupied triangles share a single occupied row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Huang curvature forbids three pairwise opposite signed contributions at a common empty row. Therefore every occupied graph triangle has a common occupied row, and the three-contact cap prevents one edge from lying in two triangles."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("occupied-eight-star"),
                DeclarationHandle.Create(Module + ".occupiedK44_star"),
                H("Complete bipartite equality forces a full empty-row neighborhood"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a four-by-four occupied graph, root-neighbor double flips use the four occupied axes and empty partner axes. The other three vertices on the root side force all empty partners to agree. The eight columns are precisely the neighbors of the resulting empty row."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/PrimeContactCardinalityGap"))]));
}
