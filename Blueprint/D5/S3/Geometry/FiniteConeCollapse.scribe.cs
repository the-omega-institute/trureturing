using StrataLint.Engine;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteConeCollapseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteConeCollapse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        GeneralHeader("D5/S3/Geometry/FiniteConeCollapse",
            "Coordinate truncation and cone contraction give a based equivalence for the actual cone quotient.",
            "finite-cone-collapse",
            Anchor.ParseCanonical("mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic"),
            Anchor.ParseCanonical("mathlib/module/Mathlib.Topology.Homotopy.Equiv")),
        H("Finite cone collapse"),
        Blocks(
            Node("subcomplex-subcomplexpair", "SubcomplexPair", "Finite subcomplex data", "An ambient finite complex, an included subcomplex, and an actual face of the subcomplex suffice for the coordinate collar. No cone apex, full-subcomplex condition, collar, or extension property is supplied.", DescribeRole.Definition),
            new DocumentBlock.Section(H("Distance control by outside mass"), Blocks(Paragraph(Text("SubcomplexPair.delta: Take the minimum over actual subcomplex faces of the sum of coordinates outside the face. Finiteness and the supplied face witness make this minimum defined.")))),
            new DocumentBlock.Section(H("Normalized coordinate truncation"), Blocks(Paragraph(Text("SubcomplexPair.deform: At time s truncate each coordinate x(v) to max(x(v)-s*min(delta,epsilon),0), then divide by the sum. Here epsilon is one divided by twice (card(V)+1). Every original face and every absent vertex coordinate is retained.")))),
            Node("subcomplex-simplex-data", "simplex_data", "Coordinate simplex data", "Each realization point has nonnegative coordinates summing to one, as read from its actual face witness.", DescribeRole.Theorem),
            new DocumentBlock.Section(H("Continuous coordinates"), Blocks(Paragraph(Text("SubcomplexPair.coord_continuous: Coordinate evaluation is continuous in the original subspace topology.")))),
            Node("subcomplex-mem-faces", "mem_faces", "The actual finite face collection", "Filtering all finite vertex subsets gives exactly the specified subcomplex faces.", DescribeRole.Theorem),
            Node("subcomplex-faces-nonempty", "faces_nonempty", "An inhabited face collection", "The supplied subcomplex face is retained by the finite face filter.", DescribeRole.Theorem),
            Node("subcomplex-outsidemass-nonneg", "outsideMass_nonneg", "Nonnegative outside mass", "Outside mass is a finite sum of nonnegative coordinates.", DescribeRole.Theorem),
            Node("subcomplex-continuous-outsidemass", "continuous_outsideMass", "Continuous outside mass", "Each outside mass is a finite sum of continuous coordinate functions.", DescribeRole.Theorem),
            new DocumentBlock.Section(H("Nonnegative face minimum"), Blocks(Paragraph(Text("SubcomplexPair.delta_nonneg: The minimum of the actual outside masses is nonnegative.")))),
            new DocumentBlock.Section(H("Continuous face minimum"), Blocks(Paragraph(Text("SubcomplexPair.continuous_delta: The face collection is fixed and finite, so its inhabited minimum of continuous outside masses is continuous.")))),
            Node("subcomplex-delta-witness", "delta_witness", "An attaining face", "A face of the actual subcomplex attains the finite minimum, without any chosen vertex or cone structure.", DescribeRole.Theorem),
            Node("subcomplex-outside-coord-le", "outside_coord_le", "Control of each exterior coordinate", "A coordinate outside a face is bounded by that face's outside mass, using coordinate nonnegativity.", DescribeRole.Theorem),
            new DocumentBlock.Section(H("Exact vanishing locus"), Blocks(Paragraph(Text("SubcomplexPair.delta_eq_zero_iff: If the minimum is zero, its attaining face contains the whole support by the exterior-coordinate bound. Conversely the face representing a subcomplex point has zero outside mass. Thus delta vanishes exactly on the actual realized subcomplex.")))),
            new DocumentBlock.Section(H("Positive truncation scale"), Blocks(Paragraph(Text("SubcomplexPair.epsilon_pos: For a SubcomplexPair V, one divided by twice (card(V)+1) is positive. The pair's face witness requires at least one vertex. When V is empty, the unrestricted FiniteSubcomplexCylinder.retraction takes its no-faces branch and projects to the bottom.")))),
            Node("subcomplex-card-mul-epsilon", "card_mul_epsilon", "The total truncation budget", "The vertex count times epsilon is at most one half.", DescribeRole.Theorem),
            Node("subcomplex-theta-nonneg", "theta_nonneg", "Nonnegative truncation threshold", "The smaller of delta and epsilon is nonnegative.", DescribeRole.Theorem),
            Node("subcomplex-denominator-bound", "denominator_bound", "Uniform denominator bound", "Each truncated coordinate is at least x(v)-epsilon. Summing and using the coordinate sum one and the total truncation budget gives a denominator at least one half for every point and every time.", DescribeRole.Theorem),
            Node("subcomplex-denominator-pos", "denominator_pos", "A positive normalizer", "The uniform one-half lower bound makes every normalization denominator positive.", DescribeRole.Theorem),
            Node("subcomplex-deform-mem-face", "deform_mem_face", "Exact face preservation", "Normalization preserves nonnegativity and total mass one; coordinates outside the original face remain zero after truncation. Thus the deformation stays inside that original affine face.", DescribeRole.Theorem),
            new DocumentBlock.Section(H("Jointly continuous deformation"), Blocks(Paragraph(Text("SubcomplexPair.continuous_deform: The coordinatewise maximum and fixed finite sum are continuous, and the denominator never vanishes. Subtype continuity gives continuity jointly in time and point.")))),
            new DocumentBlock.Section(H("The exact initial map"), Blocks(Paragraph(Text("SubcomplexPair.deform_zero: At time zero the coordinates are unchanged and the normalizer is one.")))),
            new DocumentBlock.Section(H("Exact subcomplex fixing"), Blocks(Paragraph(Text("SubcomplexPair.deform_fixed: On the subcomplex delta is zero. Every truncated coordinate and the normalizer are unchanged at every time, hence every subcomplex point is fixed exactly.")))),
            Node("subcomplex-deform-one-mem-subcomplex", "deform_one_mem_subcomplex", "Collar entry into an actual face", "When delta is at most epsilon, choose a subcomplex face attaining delta. Every coordinate outside it is at most delta and is killed by time-one truncation. The normalized endpoint lies in that actual subcomplex face.", DescribeRole.Theorem),
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
            Node("cone-set", "coneSet", "The realized subcomplex",
                "Inside the ambient coordinate realization, the cone set is exactly the set of points belonging to the coordinate realization of C.",
                DescribeRole.Definition),
            Node("apex-point", "apexPoint", "The based coordinate vertex",
                "The basepoint is the coordinate vector with entry one at p and zero at every other vertex.",
                DescribeRole.Definition),
            Node("controlled-homotopy", "controlledHomotopy", "Coordinate truncation and cone contraction",
                "For each cone face, sum the coordinates outside that face, and take the minimum of these finitely many sums. This continuous nonnegative function vanishes exactly on the cone. Truncate every coordinate by the smaller of that minimum and 1 divided by twice the number of ambient vertices plus two, then normalize. Throughout the unit interval the denominator is at least one half, the support stays in the original face, and points sufficiently near the cone enter an actual cone face. A continuous collar coefficient then turns on the linear contraction to p only after truncation has reached that face. The resulting ambient homotopy starts at the identity, preserves the cone, finishes by sending the cone to p, and fixes p throughout.",
                DescribeRole.Definition),
            Node("collapse-relation", "collapseSetoid", "The actual collapse relation",
                "Two points are related exactly when they are equal or both belong to the realized cone. The quotient carries the quotient topology.",
                DescribeRole.Definition),
            Node("quotient-map", "quotientMap", "The continuous quotient map",
                "The forward map sends a point to its class under the actual collapse relation.",
                DescribeRole.Definition),
            Node("collapse-inverse", "collapseInverse", "An explicit continuous inverse up to homotopy",
                "The final controlled deformation is constant on every collapse fiber. Its quotient lift is the continuous inverse map and sends the cone class to p.",
                DescribeRole.Definition),
            Node("based-collapse", "basedCollapse", "Both based inverse homotopies",
                "The ambient controlled deformation is a homotopy from the identity to the quotient map followed by the inverse, relative to p. Composing the deformation with the quotient map is constant on each collapse fiber at every time, so it descends to the second homotopy, from the quotient identity to the inverse followed by the quotient map, relative to the cone class. Joint continuity follows from Mathlib's quotient-product lifting theorem using local compactness of the unit interval.",
                DescribeRole.Definition),
            Node("collapse-equivalence", "collapseEquiv", "Based homotopy equivalence of the actual quotient",
                "For every finite cone pair, the actual quotient map is a homotopy equivalence with the displayed inverse and both displayed based homotopies. This is the finite cone collapse lemma. It does not settle the additional join, graph substitution, or zero-vertex conventions of Carnero Bravo's Question 22.",
                DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
