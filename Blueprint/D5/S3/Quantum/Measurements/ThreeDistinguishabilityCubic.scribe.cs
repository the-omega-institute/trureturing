using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurements;

internal sealed class ThreeDistinguishabilityCubicDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Measurements/ThreeDistinguishabilityCubic";
    private static readonly LibraryNoteRef Distinguishability =
        LibraryNoteRef.Create("D5/L/HilbertOperators/korzekwaetal2019distinguishing");
    private static readonly LibraryNoteRef HaagerupMethod =
        LibraryNoteRef.Create("D5/L/FiniteGroups/rajchelgasiorowskizyczkowski2018robust");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A guarded cubic decides whether a nonnegative four-point law occurs as the common squared moduli of three orthonormal columns.",
        H("A cubic criterion for three distinguishable pure states on four coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weighted-phase-columns-iff-cubic-nonneg"),
                DeclarationHandle.Create(Module + ".weighted_phase_columns_iff_cubic_nonneg"),
                H("The guarded cubic criterion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Distinguishability, HaagerupMethod),
                Blocks(
                    Paragraph(Text(
                        "Let p be a nonnegative law on four coordinates with sum one. A complex "
                        + "4 × 3 matrix W with WᴴW = I and |Wᵢⱼ|² = pᵢ exists exactly when each pᵢ ≤ 1/3 "
                        + "and some 0 < t ≤ 1 satisfies qᵢ²t − dᵢ² ≥ 0 for every i and phaseCubic(p,t) = 0, "
                        + "where qᵢ = 1 − 2pᵢ and dᵢ = 4pᵢ − 1. The statement includes repeated weights, "
                        + "the uniform law, zero weights and admissible zero radicands.")),
                    Paragraph(Text(
                        "Korzekwa, Czachórski, Puchała and Życzkowski give the pure-state column "
                        + "formulation in arXiv:1812.09083v3, PDF p. 5, Lemma 5 and Eq. (19). Completing "
                        + "W gives a unitary whose squared-modulus matrix is B = [p,p,p,1−3p]. "
                        + "Section III.B and Appendix C study the dimension-four region. Appendix C.3 "
                        + "already applies Haagerup’s order-four procedure to the repeated-column slice. "
                        + "Rajchel, Gąsiorowski and Życzkowski describe that procedure in arXiv:1804.10715v2, "
                        + "Appendix A. It completes two quadrilaterals at a common phase and tests a "
                        + "remaining block-entry modulus.")),
                    Paragraph(Text(
                        "From W, the diagonal of the projection WWᴴ gives 3pᵢ ≤ 1. Unit row phases make "
                        + "the first two columns conjugates, using the identity phase where both entries vanish. Their scaled real and imaginary parts form "
                        + "a real orthonormal pair. The third column lies in the complexification of its "
                        + "real two-dimensional orthogonal complement. Its real and imaginary parts give "
                        + "a real positive semidefinite Gram operator on that plane with trace one and "
                        + "diagonal p. In an orthonormal eigenbasis c,e with eigenvalues (1+s)/2 and "
                        + "(1−s)/2, one has cᵢ²+eᵢ² = qᵢ and s(cᵢ²−eᵢ²) = dᵢ. For s ≠ 0, take t = s². "
                        + "The terms yᵢ = 2s cᵢeᵢ satisfy yᵢ² = qᵢ²t−dᵢ² and sum to zero. For s = 0, "
                        + "p is uniform and t = 1 works with alternating signed half-units.")),
                    Paragraph(Text(
                        "For xᵢ = qᵢ²t−dᵢ², put A = x₀+x₁−x₂−x₃. The quartic is "
                        + "(A²−4x₀x₁−4x₂x₃)²−64x₀x₁x₂x₃. On nonnegative x it factors into eight "
                        + "linear forms in the square roots, with the first sign fixed. Thus a quartic "
                        + "zero is equivalent to a signed sum of the roots vanishing, including when "
                        + "one or more roots are zero. On substitution, the constant is the same quartic "
                        + "evaluated at (dᵢ²) and vanishes because Σᵢ dᵢ = 0. For the coefficient "
                        + "calculation, write x₀x₁ = f−gt+ht², x₂x₃ = j−kt+rt² and "
                        + "A²−4x₀x₁−4x₂x₃ = l+mt+nt². Expand (l+mt+nt²)²−64(f−gt+ht²)(j−kt+rt²) "
                        + "and shift the coefficients of t⁴,t³,t²,t down one degree. This gives "
                        + "the explicit polynomial of degree at most three. Its root test uses t > 0.")),
                    Paragraph(Text(
                        "Conversely an admissible cubic root gives signed roots yᵢ with zero sum. Set "
                        + "s = √t, cᵢ = √((qᵢ+dᵢ/s)/2), and choose eᵢ with magnitude √((qᵢ−dᵢ/s)/2) "
                        + "and the sign of yᵢ, taking the positive sign at zero. The identities "
                        + "Σᵢ qᵢ = 2 and Σᵢ dᵢ = 0 give unit norms. The signed sum gives c·e = 0. "
                        + "Complete c,e by a real orthonormal pair a,b. Use the columns (a−ib)/√2, "
                        + "(a+ib)/√2 and √((1+s)/2)c + i√((1−s)/2)e. Their Gram matrix is the "
                        + "identity and their squared moduli are p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("infeasible-weighted-phase-columns"),
                DeclarationHandle.Create(Module + ".infeasible_weighted_phase_columns"),
                H("A strictly sub-cap law with no three columns"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The normalized law (19999, 15001, 12000, 13000)/60000 has four distinct "
                    + "positive weights, all strictly below 1/3. The cubic is "
                    + "(187047147977039896t³ + 345304640904270873t² + 158219836231921608t "
                    + "+ 14368342729440656)/11390625000000000000. Every numerator coefficient "
                    + "is positive, so it has no positive root. The forward implication excludes an "
                    + "isometry for this law and shows that the row cap alone is insufficient for "
                    + "the three-column pure-state condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("feasible-weighted-phase-columns"),
                DeclarationHandle.Create(Module + ".feasible_weighted_phase_columns"),
                H("A strictly sub-cap law with three columns"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Use the normalized law (29, 27, 25, 19)/100, whose four positive weights are "
                    + "distinct and below 1/3. Its cubic is "
                    + "−32(44631t³−55970t²+15072t−1152)/244140625. It is positive at t = 1/2 "
                    + "and negative at t = 1. The intermediate value theorem gives a root "
                    + "strictly between these endpoints. Each radicand is already nonnegative "
                    + "at 1/2, and it increases weakly with t. The reverse implication supplies "
                    + "the prescribed three orthonormal columns."))),
                DescribeRole.Theorem),
            Theorem("weighted-phase-columns-iff-cubic", "weighted_phase_columns_iff_cubic",
                "Strictly positive weights",
                "A strictly positive normalized law satisfies the same criterion. The positive "
                + "entry supplies the fixed-bath specialization at positive Gibbs weights."),
            Theorem("conjugate-pair-gauge-nonneg", "conjugate_pair_gauge_nonneg",
                "Gauging two equal-modulus entries",
                "For equal positive squared moduli a unit phase makes the two entries conjugate. "
                + "At squared modulus zero both entries vanish and the unit phase can be one."),
            Theorem("real-gram-entry", "real_gram_entry", "Real column Gram entries",
                "Expanding the transpose product of a real isometry gives the column inner "
                + "products as the Kronecker delta."),
            Theorem("complete-real-pair", "complete_real_pair", "Real orthogonal completion",
                "An orthonormal pair on four real coordinates extends to an orthogonal matrix "
                + "whose first two columns are the given pair."),
            Theorem("complex-gram-re", "complex_gram_re", "Real part of the complex Gram matrix",
                "The real part adds the dot products of the real parts and of the imaginary "
                + "parts of the two columns."),
            Theorem("complex-gram-im", "complex_gram_im", "Imaginary part of the complex Gram matrix",
                "The imaginary part subtracts the second mixed dot product from the first, "
                + "as required by conjugation of the first column."),
            Definition("cubic-after-constant", "cubicAfterConstant", "The coefficient calculation",
                "For generic affine radicands uᵢt−vᵢ, the coefficient formula drops the constant "
                + "and shifts degrees down by one. The boundary certificate evaluates this formula "
                + "at the exact vertex."),
            Definition("phase-cubic", "phaseCubic", "The polynomial for the guarded test",
                "The explicit coefficient formula is the expansion of the quartic at xᵢ = qᵢ²t−dᵢ² "
                + "with the constant term removed and the powers shifted down. Normalization makes "
                + "the removed term zero."),
            Definition("complement-diagonal", "q", "The complementary projection diagonal",
                "The coordinate qᵢ = 1 − 2pᵢ is the diagonal of the real projection orthogonal to "
                + "the real pair obtained from the first two columns."),
            Definition("diagonal-difference", "d", "The diagonal difference",
                "The coordinate dᵢ = 4pᵢ − 1 is the spectral gap times the difference of the two "
                + "squared real eigenbasis coordinates."),
            Definition("infeasible-weights", "infeasibleWeights", "The infeasible law",
                "The four coordinates are (19999, 15001, 12000, 13000)/60000."),
            Definition("feasible-weights", "feasibleWeights", "The feasible law",
                "The four coordinates are (29, 27, 25, 19)/100."))));

    private static DocumentBlock.Describe Theorem(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static DocumentBlock.Describe Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
