using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteVertexCylinderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteVertexCylinder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A division-free vertex-cylinder retraction and homotopy extension for finite coordinate realizations.",
        H("Homotopy extension at a realized vertex"),
        Blocks(
            Node("vertex-point", "vertexPoint", "An actual realized vertex",
                "Let M be a pre-abstract simplicial complex on a finite ambient vertex type V. A singleton face {v} determines the coordinate vertex with entry one at v and zero elsewhere, as a point of the existing geometric realization of M. Vertices absent from M need not be realized.",
                DescribeRole.Definition),
            Node("cylinder", "Cylinder", "The bottom and vertex cylinder",
                "Inside the realization times the unit interval, the boundary subspace consists exactly of pairs whose time is zero or whose spatial coordinate is the chosen realized vertex.",
                DescribeRole.Definition),
            Node("retraction", "retraction", "A continuous coordinate retraction",
                "For a point x and time t, write s=x_v and b=t s. Replace every coordinate x_w with w different from v by max(x_w-b,0), and assign the remaining mass to coordinate v. The new height is max(b+s-1,0). All new coordinates are nonnegative and sum to one. If the original face omits v, then s=0 and the point is unchanged; otherwise the new support stays in that face. A positive new height forces every coordinate other than v to vanish. Finite sums and maxima make both components jointly continuous, without division or a nonempty-link assumption.",
                DescribeRole.Definition),
            Node("fixed", "retraction_fixed", "The boundary is fixed pointwise",
                "The continuous map to the bottom-or-vertex cylinder restricts to the identity on that entire subspace. At time zero the spatial point is unchanged and the new height is zero; at the chosen vertex the spatial point remains the vertex and the new height is the original time. Singleton complexes are included.",
                DescribeRole.Theorem),
            Node("extension", "vertex_homotopy_extension", "Arbitrary target-valued homotopy extension",
                "For every topological space Y, every continuous map f from the finite coordinate realization to Y, and every continuous path h in Y starting at f(v), there is a jointly continuous map F on the realization times the unit interval satisfying F(x,0)=f(x) for all x and F(v,t)=h(t) for all t. The boundary map glues f and h along two closed sets and then composes with the explicit retraction. No separation property of Y is required. This establishes homotopy extension at each actual vertex; it does not assert homotopy extension for arbitrary subcomplexes or settle the remaining graph and join steps of Question 22.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
