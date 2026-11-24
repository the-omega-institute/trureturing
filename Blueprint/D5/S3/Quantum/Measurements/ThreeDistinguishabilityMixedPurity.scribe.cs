using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ThreeDistinguishabilityMixedPurityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/ThreeDistinguishabilityMixedPurity";
    private static readonly LibraryNoteRef Distinguishability =
        LibraryNoteRef.Create("D5/L/HilbertOperators/korzekwaetal2019distinguishing");
    private static readonly LibraryNoteRef JointNumericalRange =
        LibraryNoteRef.Create("D5/L/HilbertOperators/lipoon2000jointnumericalrange");
    private static readonly LibraryNoteRef HaagerupMethod =
        LibraryNoteRef.Create("D5/L/FiniteGroups/rajchelgasiorowskizyczkowski2018robust");
    private static readonly LibraryNoteRef CentralRay =
        LibraryNoteRef.Create("D5/L/Convexity/bengtssonericssonkustadejzyczkowski2004unistochastic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A guarded cubic decides membership in the mixed three-distinguishability region for every four-coordinate probability law.",
        H("The four-level mixed three-distinguishability region"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("in-region-iff-cubic"),
                DeclarationHandle.Create(Module + ".inRegion_iff_cubic"),
                H("Exact membership on the closed simplex"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Distinguishability, JointNumericalRange, HaagerupMethod, CentralRay),
                Blocks(
                    Paragraph(Text(
                        "Let pᵢ ≥ 0 and Σᵢ pᵢ = 1. The predicate InRegion requires three positive "
                        + "semidefinite trace-one matrices with common diagonal p and pairwise zero "
                        + "products. It holds exactly when every pᵢ ≤ 1/3 and there is a real t with "
                        + "0 < t ≤ 1, xᵢ = (1−2pᵢ)²t−(4pᵢ−1)² ≥ 0 for all i, and phaseCubic(p,t) = 0.")),
                    Paragraph(Text(
                        "The cap is the diagonal bound from the projection WWᴴ for an isometry W with "
                        + "three columns of common squared moduli p. Gauge two columns as conjugates. "
                        + "For their real complementary plane with orthonormal axes c,e, the diagonal "
                        + "equations are cᵢ²+eᵢ² = qᵢ = 1−2pᵢ and s(cᵢ²−eᵢ²) = dᵢ = 4pᵢ−1, where s "
                        + "is the difference of the compressed eigenvalues. For s ≠ 0 put t = s². The "
                        + "numbers 2s cᵢeᵢ square to xᵢ, and their signed sum vanishes by orthogonality. "
                        + "If s = 0, p is uniform and t = 1 admits signed half-units with sum zero.")),
                    Paragraph(Text(
                        "For A = x₀+x₁−x₂−x₃, the quartic (A²−4x₀x₁−4x₂x₃)²−64x₀x₁x₂x₃ "
                        + "is the product of the eight real signed sums of the square roots with the "
                        + "first sign fixed. A zero is therefore equivalent to actual real roots yᵢ with "
                        + "yᵢ² = xᵢ and Σᵢ yᵢ = 0, even when roots vanish. Substituting xᵢ = qᵢ²t−dᵢ² "
                        + "gives zero constant coefficient because Σᵢ dᵢ = 0. The quartic is "
                        + "t phaseCubic(p,t), so the division only uses the positive root range.")),
                    Paragraph(Text(
                        "Given an admissible root, put s = √t and take cᵢ ≥ 0 with square "
                        + "(qᵢ+dᵢ/s)/2. Give eᵢ the sign of yᵢ and square (qᵢ−dᵢ/s)/2, taking the "
                        + "positive sign at zero. This choice yields 2s cᵢeᵢ = yᵢ, including zero roots. "
                        + "The sums of the squared coordinates are one, and the signed sum makes c·e = 0. "
                        + "Completing the pair over ℝ supplies the conjugate columns. The third column "
                        + "uses the c and e components in phase quadrature and the eigenvalues "
                        + "(1+s)/2 and (1−s)/2.")),
                    Paragraph(Text(
                        "Korzekwa, Czachórski, Puchała and Życzkowski give the pure-state and repeated-column "
                        + "equivalence in Lemma 5 of arXiv:1812.09083v3. Lemma 6 gives pure replacement "
                        + "on the saturated cap. Section III.B and Appendix C study the four-dimensional "
                        + "region, and Appendix C.3 reports numerical tests on [p,p,p,1−3p] using "
                        + "Haagerup’s order-four procedure as presented by Rajchel, Gąsiorowski and "
                        + "Życzkowski in arXiv:1804.10715v2, Appendix A.")),
                    Paragraph(Text(
                        "On the special line p(u) = (1−3u,1+u,1+u,1+u)/4, the matrix in Appendix C.2, "
                        + "Eq. (C37), is the type-I central ray of Bengtsson et al., arXiv:math/0402325v2, "
                        + "§IV, Eqs. (35)–(40), and Appendix C. Their phase equations require "
                        + "L = (1−3u)/(1+u) ≤ 1 on this line, excluding −1/9 ≤ u < 0. The uniform "
                        + "endpoint u = 0 has a Hadamard lift. This ray parameter u labels the law.")),
                    Paragraph(Text(
                        "The product refutation in ThreeDistinguishabilityProductRefutation supplies a "
                        + "point in the region missed by every labelling of the product ansatz in Eq. (30). "
                        + "The cubic equivalence decides membership in both directions at every point "
                        + "of the simplex. As a topological corollary, the region is compact and closed. "
                        + "The equal-row-modulus equations cut out a closed subset of the compact "
                        + "complex Stiefel manifold of 4 × 3 isometries. The map taking the squared "
                        + "moduli of the first column is continuous and has image exactly the mixed region. "
                        + "This paragraph gives the compactness argument in prose."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("in-region-iff-weighted-isometry"),
                DeclarationHandle.Create(Module + ".inRegion_iff_weighted_isometry"),
                H("Mixed and pure witnesses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Distinguishability, JointNumericalRange),
                Blocks(Paragraph(Text(
                    "Pairwise orthogonality of the supports bounds the sum of their ranks by four. "
                    + "Each rank is at least one because the trace is one. After permuting the states, "
                    + "the first two are rank one and have orthogonal unit representatives. Gauge this "
                    + "pair simultaneously and replace the third state in its real complementary "
                    + "plane. The result is a complex isometry with the required common row moduli. "
                    + "The converse uses the three column projectors and gives the simplex equations "
                    + "from the squared moduli of any unit column."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pure-replacement-for-equal-moduli"),
                DeclarationHandle.Create(Module + ".pure_replacement_for_equal_moduli"),
                H("A common row gauge preserves the diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(JointNumericalRange),
                Blocks(Paragraph(Text(
                    "The two orthogonal pure columns have equal moduli on each row. Choose a common "
                    + "unit row phase to make their entries conjugate, using the identity where "
                    + "both entries vanish. Conjugate the remaining density by the same unit diagonal "
                    + "matrix. This preserves trace, positivity, diagonal and the two annihilations. "
                    + "After real compression, undo the gauge on the replacement. Its squared moduli "
                    + "are the original remaining diagonal, which can be arbitrary."))),
                DescribeRole.Theorem),
            Theorem("weighted-isometry-of-in-region", "weighted_isometry_of_inRegion",
                "Three pure columns from mixed witnesses",
                "Extract two rank-one unit columns, apply equal-modulus replacement to the remaining density, "
                + "and use orthogonality and the common diagonal to obtain the target isometry."),
            Theorem("in-region-of-weighted-isometry", "inRegion_of_weighted_isometry",
                "Column projectors witness membership",
                "The outer products of the unit columns have trace one, use the prescribed diagonal, "
                + "and have pairwise zero products because the column inner products vanish."),
            Theorem("one-zero-feasible", "one_zero_feasible",
                "A vertex with one zero weight",
                "At p = (0,1/3,1/3,1/3), t = 1 satisfies the cap and makes each radicand zero. "
                + "Exact substitution gives phaseCubic(p,1) = 0. Any law in the region with a "
                + "zero entry is a permutation of this law by normalization and the cap. "
                + "Permuting coordinates transports the witnesses."),
            Theorem("infeasible-not-in-region", "infeasible_not_inRegion",
                "A strictly sub-cap law excluded from the mixed region",
                "The law (19999,15001,12000,13000)/60000 is positive and normalized with every entry "
                + "strictly below 1/3. Its cubic has strictly positive coefficients and hence no "
                + "positive root. The weighted-column obstruction transfers to InRegion."))));

    private static DocumentBlock.Describe Theorem(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
