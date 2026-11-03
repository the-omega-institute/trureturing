using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteSimplicialOpenCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteSimplicialOpenCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive coordinate stars of a finite complex.", H("Positive coordinate stars of a finite complex"), Blocks(
            Node("vertexopen", "vertexOpen", "Open vertex stars",
                "For a finite linearly ordered vertex type V and pre-abstract simplicial complex K, the carrier is the subtype of real coordinate vectors in FiniteConeCollapse.realization K. The star of v consists exactly of points with strictly positive v coordinate. Ghost vertices give empty stars.", DescribeRole.Definition),
            Node("vertexopen-cover", "vertexOpen_cover", "A cover of the actual carrier",
                "The vertex stars are open in the coordinate subspace topology and cover the entire carrier. The existing FiniteConeCollapse.realization_mem_iff identifies a realized point with a point in an actual face simplex, giving nonnegative coordinates summing to one, so some coordinate is positive. The carrier may be empty.", DescribeRole.Theorem),
            Node("face-of-nonempty-intersection", "face_of_nonempty_intersection", "Intersections detect faces",
                "If a nonempty finite vertex set has a point in its positive-coordinate intersection, it is a face of K. Positivity places all selected vertices in a support face of that same point; downward closure then applies.", DescribeRole.Theorem),
            Node("intersectioncontraction", "intersectionContraction", "Straight-line contraction",
                "For any actual face s, the equal-weight barycenter lies in its intersection. The straight segment from each intersection point to that barycenter stays in the original support face and retains positivity on s. This gives a continuous homotopy from the identity to the constant barycenter map.", DescribeRole.Definition),
            Node("contractible-intersection", "contractible_intersection", "Contractible face intersections",
                "Every actual face has a contractible positive-coordinate intersection, with the displayed barycenter and homotopy. The empty intersection is the whole carrier and is not asserted to be contractible.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
