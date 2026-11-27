using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Lorentz;

internal sealed class ReggeSchlafli4DDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Lorentz/ReggeSchlafli4D.";
    private static readonly LibraryNoteRef Regge =
        LibraryNoteRef.Create("D5/L/LieTheory/regge1961calculus");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minkowski facet closure gives the Euclidean Schläfli identity and the first variation of the four-dimensional Regge action.",
        H("Euclidean Schläfli identity and Regge variation"),
        Blocks(
            Entry("facet-normal", "facet_normal", "Outward unit facet normals",
                "The outward unit normal is the negative normalized gradient of the barycentric coordinate. "
                + "The coordinate vanishes on the opposite facet and is one at its excluded vertex."),
            Entry("facet-closure", "facet_closure", "Minkowski facet closure",
                "Each facet has positive Euclidean volume. By the base-and-height formula, its volume is the simplex volume "
                + "times the dimension and the norm of its barycentric gradient. Summing the weighted normals gives zero "
                + "because the barycentric coordinates sum to one."),
            Entry("dihedral-cosine", "dihedral_cosine", "Interior dihedral cosine",
                "The cosine of the interior dihedral angle is the negative inner product of the outward unit normals. "
                + "Projecting one gradient into the other facet gives a nonzero vector for distinct facets."),
            Entry("euclidean-schlafli", "euclidean_schlafli", "Euclidean Schläfli differential identity",
                "In every dimension at least two, differentiable vertex paths through nondegenerate simplices have zero "
                + "sum of ridge volumes times interior dihedral angle derivatives. The base-and-height formula applied twice "
                + "gives the ridge volume as the dimension times its predecessor, the simplex volume, the product of the "
                + "gradient norms and the sine of the angle. The derivative of arccos cancels the sine. Contracting the "
                + "differentiated normal inner products with the gradient norms then uses Minkowski facet closure. "
                + "Unit norms give zero diagonal derivatives, and symmetry counts each distinct pair twice."),
            Entry("tetrahedron-schlafli", "tetrahedron_schlafli", "Tetrahedron edge-length identity",
                "In dimension three the ridges are edges and their volumes are the distances between their endpoints."),
            Entry("four-simplex-schlafli", "four_simplex_schlafli", "Four-simplex triangle-area identity",
                "In dimension four the ten ridges are triangles and their volumes are their Euclidean areas."),
            Entry("regge-variation", "regge_variation", "First variation of the Regge action",
                "Each four-simplex embeds its ten local triangles in the finite type of global hinges. Its triangle "
                + "areas agree with the differentiable area functions on those hinges. A deficit is two pi minus the sum "
                + "of incident interior dihedral angles. The product rule gives area and angle terms. Exchanging the "
                + "finite sums groups the angle terms by simplex, where the four-simplex identity cancels each group. "
                + "The derivative is the sum of each hinge area derivative times its deficit."),
            Entry("regular-edge-length", "regular_edge_length", "Regular four-simplex edge length",
                "The centered vertex Gram matrix has entries equal to half the squared edge length times a Kronecker "
                + "delta minus one fifth of that factor. It yields the given positive length for every edge."),
            Entry("regular-dihedral-angle", "regular_dihedral_angle", "Regular four-simplex dihedral angle",
                "The barycentric gradients are a common positive multiple of the centered vertices. Their normalized "
                + "inner product is negative one quarter on distinct vertices, so the interior angle is arccos of one quarter. "
                + "Minkowski facet closure applies to these same normals."),
            Entry("regular-triangle-area", "regular_triangle_area", "Regular four-simplex triangle area",
                "The perpendicular residual of the third vertex from an edge line has length square root of three times "
                + "half the edge length. The triangle area is square root of three times one quarter of the squared edge length."),
            Entry("regular-scaling", "regular_scaling_cancellation", "Uniform dilation of the regular simplex",
                "Multiplying the positive edge length by the exponential of time preserves the angle at every hinge. "
                + "Each angle derivative vanishes along this path."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Regge),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);
}
