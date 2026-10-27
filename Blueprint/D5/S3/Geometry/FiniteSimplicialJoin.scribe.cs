using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteSimplicialJoinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteSimplicialJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary quotient join and the finite coordinate simplicial join realization.",
        H("Finite simplicial join realization"),
        Blocks(
            Node("ordinary-join-relation", "ordinaryJoinSetoid", "The endpoint equivalence relation",
                "Representatives are triples (x,y,t) in the actual product of the two spaces and the closed unit interval. They are equivalent exactly when their parameters agree, their left coordinates agree unless t is one, and their right coordinates agree unless t is zero. Interior representatives retain both coordinates.", DescribeRole.Definition),
            Node("ordinary-join", "OrdinaryJoin", "The ordinary topological join",
                "The ordinary join is the quotient by the endpoint equivalence relation, with the native quotient topology of the product topology. If either factor is empty this ordinary join is empty.", DescribeRole.Definition),
            Node("simplicial-join", "simplicialJoin", "Nonempty tagged faces",
                "For complexes M on V and N on W, a face of their join is a nonempty finite subset of V disjoint union W. Each nonempty tagged block must be a face of its corresponding complex. Either block may be empty; the whole face may not. Downward closure is proved for every nonempty subface.", DescribeRole.Definition),
            Node("space", "Space", "The actual coordinate realization",
                "The factor and target spaces use FiniteConeCollapse.realization: the union of the convex hulls of coordinate vertices of actual faces, with the ambient real coordinate subspace topology. Both vertex types are finite.", DescribeRole.Definition),
            Node("representative", "representative", "Barycentric coordinates",
                "The left coordinate at v is (1-t) times x(v), and the right coordinate at w is t times y(w). Nonnegativity, total mass one and support in the disjoint sum of actual factor faces put the image in the actual join realization.", DescribeRole.Definition),
            Node("fibers", "representative_eq_iff", "Exact quotient fibers",
                "Two barycentric vectors are equal if and only if their representatives are endpoint equivalent. Summing the right coordinates recovers t. Cancellation recovers the left point when t is not one and the right point when t is not zero. At an endpoint the other block vanishes exactly as required by the ordinary join relation.", DescribeRole.Theorem),
            Node("realization-map", "realizationMap", "The continuous quotient map",
                "The barycentric map is continuous coordinate by coordinate and constant exactly on the endpoint equivalence classes, so its native quotient lift is continuous.", DescribeRole.Definition),
            Node("homeomorphism", "joinHomeomorph", "Homeomorphism of actual realizations",
                "For every pair of finite vertex types and pre-abstract simplicial complexes M and N with both actual factor realizations nonempty, their ordinary topological join is homeomorphic to the actual coordinate realization of their simplicial join. For surjectivity, sum the target's right block to obtain t and normalize each positive-mass block inside its actual factor face. For a zero-mass block, use a chosen actual point in that nonempty factor. Each factor realization is a finite union of compact convex hulls. The source quotient is therefore compact and the target is Hausdorff, so the continuous bijection is a homeomorphism. This classical bridge does not establish graph substitution, sphere-join identities, finite sphere-wedge closure or the full Question 22 of Carnero Bravo. The nonempty hypotheses exclude the ordinary-join versus augmented-empty-face convention mismatch.", DescribeRole.Definition),
            Node("formula", "joinHomeomorph_apply", "The representative formula",
                "For all actual points x and y and all interval parameters t, the homeomorphism sends the class of (x,y,t) to the vector with left block (1-t)x and right block ty, including both endpoints.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
