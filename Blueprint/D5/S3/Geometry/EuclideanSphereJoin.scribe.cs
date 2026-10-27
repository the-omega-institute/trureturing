using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class EuclideanSphereJoinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/EuclideanSphereJoin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ordinary topological join of actual Euclidean unit spheres.",
        H("Euclidean sphere joins"),
        Blocks(
            Node("unit-sphere", "UnitSphere", "Unit spheres",
                "The unit sphere is the actual metric sphere of radius one about zero, equipped with its normed-space subspace topology.", DescribeRole.Definition),
            Node("standard-sphere", "StdSphere", "Standard Euclidean spheres",
                "For each natural n, the standard sphere is the unit sphere in EuclideanSpace over the reals indexed by Fin (n+1), with the Euclidean norm. In particular n=0 is the two-point sphere in a one-dimensional vector space.", DescribeRole.Definition),
            Node("representative", "representative", "Normalized block coordinates",
                "For unit vectors x and y and t in the closed unit interval, put d=max(1-t,t). The representative map is the pair (((1-t)/d)x,(t/d)y). The positive denominator is at least one half. The product carries its native maximum norm, so the resulting vector has norm one.", DescribeRole.Definition),
            Node("exact-fibers", "representative_eq_iff", "The exact ordinary join relation",
                "For all real normed spaces E and F and all actual representatives a and b in S(E) times S(F) times the closed unit interval, their normalized block vectors agree if and only if their interval coordinates agree, their left coordinates agree unless the parameter is one, and their right coordinates agree unless it is zero. The block norms recover the two nonnegative weights, and the right weight divided by the sum of the weights recovers the parameter. A nonzero weight can be cancelled, while the endpoint block vanishes.", DescribeRole.Theorem),
            Node("quotient-map", "productSphereMap", "Descent to the actual quotient",
                "The continuous normalized block formula descends through FiniteSimplicialJoin.OrdinaryJoin, using exactly its endpoint setoid and native quotient topology.", DescribeRole.Definition),
            Node("product-homeomorphism", "productSphereHomeomorph", "The maximum norm sphere",
                "For compact unit spheres with chosen actual points x0 and y0, the ordinary join is homeomorphic to the unit sphere of the product. Given a target (u,v), write r=norm(u), s=norm(v). Its maximum block norm is one. Choose t=s/(r+s), normalize each nonzero block and use x0 or y0 for a zero block. This gives a preimage without requiring the choices to be continuous. Exact fibers give injectivity. The quotient is compact and the target is Hausdorff, so the native continuous bijection is a homeomorphism.", DescribeRole.Definition),
            Node("coordinate-point", "coordinatePoint", "Chosen coordinate points",
                "The chosen point of each standard sphere is the first coordinate vector, with coefficient one in coordinate zero and zero elsewhere.", DescribeRole.Definition),
            Node("sphere-homeomorphism", "sphereJoinHomeomorph", "The Euclidean sphere join homeomorphism",
                "For every pair of natural p and q, the ordinary join of the actual standard Euclidean spheres of dimensions p and q is homeomorphic to the actual standard Euclidean sphere of dimension p+q+1. The normalized quotient homeomorphism first reaches the maximum-norm product sphere. Native linear coordinate concatenation identifies the ambient product with the Euclidean space indexed by Fin (p+q+2). Radial normalization sends z to L(z)/norm(L(z)); the inverse sends w to L inverse(w)/norm(L inverse(w)). Nonzero images, linearity and scalar norm identities prove that the maps are inverse, and the native polar-coordinate homeomorphism supplies their continuity. No equality between the product maximum norm and the Euclidean norm is used. Both zero-dimensional sphere factors are included. Hatcher, Algebraic Topology, page 9 defines the ordinary join, and Chapter 0 Exercise 18 on page 19 states this classical sphere identity. This construction supplies a classical geometric bridge and makes no claim to resolve Carnero Bravo Question 22.", DescribeRole.Definition),
            Node("chosen-endpoint", "sphereJoinHomeomorph_coordinatePoint", "Exact coordinate endpoint",
                "For every natural p and q and every actual point y of the q-dimensional sphere, the homeomorphism sends the quotient class of (e0,y,0) exactly to the first coordinate unit vector of the target sphere. At parameter zero the normalized product vector is (e0,0). Concatenation sends it to the first target coordinate vector, whose Euclidean norm is one, so radial normalization fixes it.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
