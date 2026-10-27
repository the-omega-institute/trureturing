using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteConeCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteConeCollapse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit based homotopy inverse for collapsing a finite cone subcomplex.",
        H("Finite cone collapse"),
        Blocks(
            Node("face-simplex", "faceSimplex", "Coordinate face simplices",
                "For a finite vertex type V and a finite subset s, the face simplex consists of real coordinate vectors with nonnegative entries summing to one and with every coordinate outside s equal to zero. The simplex of the empty face is empty.",
                DescribeRole.Definition),
            Node("face-simplex-convex-hull", "faceSimplex_eq_convexHull", "Actual affine simplices",
                "For every finite subset s of V, its coordinate simplex equals the convex hull in the real coordinate space of the coordinate vertices indexed by s. Thus the coordinate model is the usual geometric simplex, including its boundary faces.",
                DescribeRole.Theorem),
            Node("realization", "realization", "Finite geometric realization",
                "The realization of a Mathlib pre-abstract simplicial complex is the union of its actual coordinate face simplices, with the subspace topology inherited from the finite real coordinate space. The ambient vertex type may contain vertices absent from the complex.",
                DescribeRole.Definition),
            Node("cone-pair", "ConePair", "An actual cone subcomplex",
                "A cone pair consists of an ambient complex M, a subcomplex C, and an apex p whose singleton is a face of C. Adjoining p to any face of C again gives a face of C. These are face conditions on the given complexes, and do not assert any extension property or homotopy equivalence. The singleton cone is included.",
                DescribeRole.Definition),
            Node("cone-set", "ConePair.coneSet", "The realized subcomplex",
                "Inside the ambient coordinate realization, the cone set is exactly the set of points belonging to the coordinate realization of C.",
                DescribeRole.Definition),
            Node("apex-point", "ConePair.apexPoint", "The based coordinate vertex",
                "The basepoint is the coordinate vector with entry one at p and zero at every other vertex.",
                DescribeRole.Definition),
            Node("controlled-homotopy", "ConePair.controlledHomotopy", "Coordinate truncation and cone contraction",
                "For each cone face, sum the coordinates outside that face, and take the minimum of these finitely many sums. This continuous nonnegative function vanishes exactly on the cone. Truncate every coordinate by the smaller of that minimum and 1 divided by twice the number of ambient vertices plus two, then normalize. Throughout the unit interval the denominator is at least one half, the support stays in the original face, and points sufficiently near the cone enter an actual cone face. A continuous collar coefficient then turns on the linear contraction to p only after truncation has reached that face. The resulting ambient homotopy starts at the identity, preserves the cone, finishes by sending the cone to p, and fixes p throughout.",
                DescribeRole.Definition),
            Node("collapse-relation", "ConePair.collapseSetoid", "The actual collapse relation",
                "Two points are related exactly when they are equal or both belong to the realized cone. The quotient carries the quotient topology.",
                DescribeRole.Definition),
            Node("quotient-map", "ConePair.quotientMap", "The continuous quotient map",
                "The forward map sends a point to its class under the actual collapse relation.",
                DescribeRole.Definition),
            Node("collapse-inverse", "ConePair.collapseInverse", "An explicit continuous inverse up to homotopy",
                "The final controlled deformation is constant on every collapse fiber. Its quotient lift is the continuous inverse map and sends the cone class to p.",
                DescribeRole.Definition),
            Node("based-collapse", "ConePair.basedCollapse", "Both based inverse homotopies",
                "The ambient controlled deformation is a homotopy from the identity to the quotient map followed by the inverse, relative to p. Composing the deformation with the quotient map is constant on each collapse fiber at every time, so it descends to the second homotopy, from the quotient identity to the inverse followed by the quotient map, relative to the cone class. Joint continuity follows from Mathlib's quotient-product lifting theorem using local compactness of the unit interval.",
                DescribeRole.Definition),
            Node("collapse-equivalence", "ConePair.collapseEquiv", "Based homotopy equivalence of the actual quotient",
                "For every finite cone pair, the actual quotient map is a homotopy equivalence with the displayed inverse and both displayed based homotopies. This is the finite cone collapse lemma. It does not settle the additional join, graph substitution, or zero-vertex conventions of Carnero Bravo's Question 22.",
                DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
