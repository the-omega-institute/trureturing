using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteConeUnionWedgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteConeUnionWedge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quotient wedge for a finite union along a nonempty cone.",
        H("Finite cone union wedge"),
        Blocks(
            Node("subset-relation", "subsetSetoid", "Subset collapse relation",
                "For any subset C of a space, two points are related exactly when they are equal or both belong to C.", DescribeRole.Definition),
            Node("wedge-points", "wedgePoints", "Two distinguished points",
                "For points a of X and b of Y, the distinguished subset of the disjoint sum consists exactly of inl a and inr b. The wedge is its collapse quotient with the quotient topology.", DescribeRole.Definition),
            Node("closed-cover", "CollapseCover", "A closed cover with controlled overlap",
                "Two continuous injective closed maps from X and Y cover Z. Every equality between points from opposite summands lies in the subset C, and both chosen basepoints map into C. These are map and subset conditions; no gluing continuity, homotopy extension property, or equivalence is assumed.", DescribeRole.Definition),
            Node("quotient-wedge-homeomorphism", "quotientWedgeHomeomorph", "The actual quotient homeomorphism",
                "The wedge of the actual quotients of X and Y by the preimages of C is homeomorphic to Z modulo C. The map from the disjoint sum to Z is a continuous closed surjection, hence a quotient map. After descending on both arms, the resulting quotient map has exactly the two-basepoint wedge relation as kernel. The homeomorphism is obtained from that kernel equality. The proof includes the degenerate cases in which C is a whole summand or the whole space.", DescribeRole.Definition),
            Node("realization-intersection", "realization_intersection", "Actual intersections of finite realizations",
                "For every finite vertex type V and every pair M,N of pre-abstract simplicial complexes on V, the coordinate realization of M intersect N equals the intersection of their coordinate realizations. A point represented in faces s and t belongs to the simplex of s intersect t; the coordinate sum one proves that this common face is nonempty. Downward closure then places it in both complexes. No empty face is assumed to be a face.", DescribeRole.Theorem),
            Node("cone-union", "ConeUnion", "Concrete finite cone union data",
                "The data are two finite-vertex complexes, their intersection cone, and an apex. The singleton apex is a cone face, and adjoining the apex preserves cone faces. The intersection equality is an equality of complexes, rather than an assumed topological intersection statement.", DescribeRole.Definition),
            Node("left-pair", "leftPair", "The left cone pair",
                "The left native coordinate realization contains the specified cone and has its coordinate apex as basepoint.", DescribeRole.Definition),
            Node("right-pair", "rightPair", "The right cone pair",
                "The right native coordinate realization contains the same cone and has the same coordinate apex as basepoint.", DescribeRole.Definition),
            Node("union-pair", "unionPair", "The union cone pair",
                "The ambient complex is the actual union of the two face collections. The specified intersection cone is a subcomplex of that union.", DescribeRole.Definition),
            Node("homotopy-equivalence", "homotopyEquiv", "The cone-union wedge equivalence",
                "For every ConeUnion, the actual coordinate realization of the union is homotopy equivalent to the quotient wedge of the two native coordinate realizations at their common apex. Each realization is closed because it is a finite union of closed convex hulls. The proved realization intersection identity establishes the exact overlap. Compose the existing explicit finite cone collapse of the union, the actual quotient homeomorphism, and the inverse of the wedge map induced by the two local cone collapses. Both local inverse homotopies are relative to the apex or its quotient class. Their disjoint-sum homotopies descend jointly continuously to the wedge by the quotient-product lifting theorem, using local compactness of the unit interval. This is the classical cone-union topology used in the single-vertex substitution route of Carnero Bravo, arXiv:2505.06457v2, Question 22. It asserts neither a solution of that question nor novelty; the graph, join, hereditary induction and sphere-model obligations remain outside this theorem.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
