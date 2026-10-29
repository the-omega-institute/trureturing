using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Orthogonality;

internal sealed class RationalSixAxisCoverDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Orthogonality/RationalSixAxisCover.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six explicit rational axes cover the real unit two-sphere by relatively open orthogonality-free sets.",
        H("A rational six-axis open cover"),
        Blocks(
            Node("ambient-space", "Space", "Real Euclidean three-space",
                "The ambient space is EuclideanSpace over the reals indexed by Fin 3, with its standard Euclidean norm and inner product.", DescribeRole.Definition),
            Node("unit-sphere", "UnitSphere", "The standard unit two-sphere",
                "The carrier is Metric.sphere zero one in EuclideanSpace over the reals indexed by Fin 3. It has the ordinary subspace topology and the standard real inner product.", DescribeRole.Definition),
            Node("axes", "axis", "The six rational axes",
                "In order, the six vectors are (1,2,0), (1,-2,0), (0,1,2), (0,1,-2), (2,0,1), and (-2,0,1). Each has squared Euclidean norm five. No normalization or choice of an irrational coordinate is required.", DescribeRole.Definition),
            Node("colors", "color", "Strict projection superlevels",
                "For each index i in Fin 6, the corresponding subset consists of all actual unit vectors x satisfying 5 < 2 times the square of the inner product of x with axis i. These are subsets of the entire sphere.", DescribeRole.Definition),
            Node("open-cover", "rational_six_axis_open_cover", "An open orthogonality-free cover",
                "All six subsets are open in the sphere, each excludes every orthogonal pair of unit vectors, and their indexed union is the entire sphere. Openness follows from continuity of the inner product and the strict inequality. For orthogonal unit x and y, the two-vector Bessel inequality gives the sum of their squared projections onto any one axis at most five; membership of both would make that sum greater than five. The proof uses Mathlib's Orthonormal.sum_inner_products_le. For coverage put a=abs(x0), b=abs(x1), c=abs(x2), Q=a squared plus b squared plus c squared, and M=max(a+2b,b+2c,c+2a). Write u=M-a-2b, v=M-b-2c, and w=M-c-2a. All these quantities are nonnegative. The exact identity is 3 M squared - 9 Q = uv+vw+wu+6(aw+bu+cv)+((a-b) squared+(b-c) squared+(c-a) squared)/2. Thus M squared is at least 3 Q. One of the two signed forms for each coordinate pair has squared value (abs(s)+2 abs(t)) squared. Since Q=1 on the sphere, one of the six squared projections is at least three, which satisfies the strict threshold. This supplies the upper bound six for Feldman--Wilce Question 3. It proves no lower bound and does not determine higher-dimensional covering numbers. The explicit rational construction and certificate are repository-derived; the cited paper supplies the question. Mathematical priority is unresolved.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
