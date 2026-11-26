using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement;

internal sealed class Q9DistanceThreeActiveBoundaryDocument : IScribeDocumentDefinition
{
    private const string Placement =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/";
    private const string Owner = Placement + "Q9DistanceThreeActiveBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unshared distance-three contacts constrain the degrees of active exterior rows.",
        H("Local geometry at a crossing edge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("active-boundary-degrees"),
                DeclarationHandle.Create(Owner + "active_boundary_degrees"),
                H("Two occupied and two inactive exterior neighbors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Consider two induced cubic supports at mutual separation at least three, with "
                    + "disjoint occupied directions at every distance-three contact. Assume the first "
                    + "support is balanced. An exterior vertex is active if it has a neighbor in the other "
                    + "exterior. Comparing the agreeing axes at two contacts forces the other occupied "
                    + "midpoint of any pair of support neighbors of an active vertex. Three support "
                    + "neighbors would give an occupied six-cycle, so evenness leaves exactly two. The two "
                    + "remaining common occupied directions produce exterior neighbors. If either were "
                    + "active, its additional occupied midpoint would close a square."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9ExteriorEdgeLiftCount")),
            DocumentEdge.Dependency.Create(GidRef.Create(Placement + "Q9DistanceThreeUnsharedDirections"))
        ]));
}
