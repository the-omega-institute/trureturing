using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class SphereOrthogonalityCoverDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026spherecovers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Relatively open orthogonality-free covers of the real two-sphere need at least six sets.",
        H("Open orthogonality-free sphere covers"),
        Blocks(
            Entry("component-inner-pos", "component_inner_pos", "Components are acute",
                "In a real inner product space, every actual connected component of an orthogonality-free subset of the unit sphere has strictly positive inner products between all its points.",
                "Fix one point x of the component. The continuous function taking y to its inner product with x never vanishes there and is positive at x. Connectedness forces it to remain positive throughout the component."),
            Entry("cover-color-multiplicity", "cover_color_multiplicity", "Color multiplicity",
                "In ambient dimension n+1, a finite orthogonality-free cover with k colors has, at every unit vector x, at most k-n colors containing x. Openness is unnecessary for this counting statement.",
                "Take an orthonormal basis of the perpendicular space to x. Its n vectors require distinct colors, and none of these colors contains x. Counting these absent colors gives the bound."),
            Entry("finite-acute-refinement", "exists_finite_acute_refinement", "Finite acute refinement",
                "On a compact locally connected unit sphere, a finite open orthogonality-free cover has a finite refinement by nonempty acute actual components whose multiplicity at each point is no greater than the original color multiplicity.",
                "Index a component by its original color and its actual subset, so that equal components of one color occur only once. Components are open, cover the sphere, and have a finite subcover by compactness. At any point the projection from selected containing components to original colors is injective, since two components of one open set that meet are equal."),
            Entry("acute-normalized-map", "acute_cover_normalized_map", "The normalized cover map",
                "For a finite open acute cover with a chosen representative in each member, there is a continuous sphere self-map homotopic to the identity. Its value at x lies in the linear span of representatives of cover members containing x.",
                "Choose a subordinate partition of unity and form F(x) as the weighted sum of the representatives. Each nonzero summand has positive inner product with x, so the inner product of x with F(x) is positive. In particular F(x) is nonzero. Normalize F, and normalize the straight segment from x to F(x) to obtain the homotopy. Zero coefficients remove all representatives whose cover members do not contain x."),
            Entry("small-spans-miss-point", "map_omits_point_of_small_spans", "Small spans omit a point",
                "In a positive finite dimensional real inner product space, a sphere map supported at each point on fewer representatives than the ambient dimension omits some sphere point.",
                "There are finitely many possible subsets of the finite representative family. The span of each subset smaller than the dimension is proper. A finite union of proper real subspaces misses a vector; normalizing that vector gives a point omitted by the sphere map."),
            Entry("acute-multiplicity-contractible", "acute_cover_contractible_of_multiplicity_lt", "The acute multiplicity obstruction",
                "A finite open acute cover with multiplicities strictly smaller than the positive ambient dimension would make the sphere contractible.",
                "The normalized cover map is homotopic to the identity and omits a point. Stereographic projection identifies the punctured sphere with a real vector space, which is contractible. The map is therefore nullhomotopic, so the identity is nullhomotopic as well."),
            Entry("open-cover-multiplicity-contractible", "open_cover_contractible_of_multiplicity_lt", "The original color multiplicity obstruction",
                "In ambient dimension n+1, a relatively open orthogonality-free cover whose original point multiplicities are below n+1 makes the sphere contractible.",
                "Pass to the finite acute component refinement, which preserves the original color multiplicity. Apply the normalized-map and omitted-point obstruction."),
            Entry("low-color-contractible", "low_color_cover_contractible", "Too few colors force a contraction",
                "In ambient dimension n+1, an open orthogonality-free cover by at most 2n sets would make the sphere contractible. No component, acuteness, refinement or multiplicity hypothesis is assumed here.",
                "The orthogonal-complement count bounds every original color multiplicity by n. Finite refinement by actual acute components preserves this bound. Since n is smaller than the ambient dimension n+1, the acute multiplicity obstruction applies."),
            Entry("sphere-open-cover-lower-bound", "sphere_open_orthogonality_free_cover_lower_bound", "The general lower bound",
                "For every natural n at least two and every finite family of relatively open subsets of the real unit sphere in n dimensions, if the family covers the sphere and no member contains an orthogonal pair, then its size k satisfies 2n-1 at most k. Neither connectedness of the cover members nor any noncontractibility premise is required.",
                "If k were at most 2n-2, the preceding construction would contract the sphere. The sphere obstruction obtained from the existing simplex Brouwer theorem rules this out. This general lower estimate and the normalized weighted-sum mechanism are antecedents of Blondal, Hatami, Hatami, Lalov and Tretiak, arXiv:2606.06148v1, Theorem 2.1 (COLT 2026, Theorem 2). Here the dimension-two case is consumed by the perpendicular-circle step of the lower bound six. No priority or novelty claim is made."),
            Entry("sphere-three-absent-colors", "sphere_three_absent_colors", "Three colors absent at each point",
                "For every relatively open orthogonality-free finite cover of the real two-sphere and every unit vector x, at least three original colors omit x.",
                "Use an orthonormal basis of the perpendicular plane to identify its unit circle isometrically with the real unit circle. A color containing x has no point on this perpendicular circle. Restrict the remaining colors along the continuous isometry; they remain relatively open and orthogonality-free and cover the circle. The dimension-two general lower bound requires at least three such colors."),
            Entry("sphere-two-lower-six", "sphere_two_open_orthogonality_free_cover_lower_six", "The lower bound six",
                "Every finite relatively open orthogonality-free cover of the unit sphere in real Euclidean three-space has at least six members. Cover members may overlap and need not be connected.",
                "Assume at most five colors. At every sphere point the perpendicular-circle result excludes at least three colors, leaving multiplicity at most two. The original-color multiplicity obstruction contracts the two-sphere, contradicting the Brouwer sphere obstruction. The exact triangular lower bound is a known consequence of Proposition 4.1 in the OpenAI September 23 manuscript and its Lean Admissible.label_bound; this proof uses a topological cover construction and claims no new mathematical priority. Together with a separately verified six-set cover it gives the exact value six."))));

    private static DocumentBlock Entry(string id, string declaration, string title,
        string statement, string proof) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Topology/SphereOrthogonalityCover." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))), DescribeRole.Theorem);
}
