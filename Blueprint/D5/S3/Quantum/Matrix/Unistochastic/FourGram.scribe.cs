using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Unistochastic;

internal sealed class UnistochasticFourGramDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Matrix/Unistochastic/FourGram.";
    private static readonly LibraryNoteRef Haagerup =
        LibraryNoteRef.Create("D5/L/FiniteGroups/rajchelgasiorowskizyczkowski2018robust");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two coupled planar Gram matrices characterize unistochasticity on the closed order-four Birkhoff polytope.",
        H("Exact order-four phase completion"),
        Blocks(
            Definition("top-diagonal", "q", "First row pair",
                "For the real four by four matrix B and column i, qᵢ = B₀ᵢ B₁ᵢ."),
            Definition("bottom-diagonal", "p", "Second row pair",
                "For the real four by four matrix B and column i, pᵢ = B₂ᵢ B₃ᵢ."),
            Definition("coupling", "coupling", "The difference of the two phase Grams",
                "Write the rows of B as vectors a, b, e, f. The coupling C is "
                + "(aaᵀ + bbᵀ − eeᵀ − ffᵀ)/2 + diag(e + f − 1/2), with the scalar "
                + "subtracted in every coordinate."),
            Definition("coupled-planar-grams", "CoupledPlanarGrams", "Feasibility of a common Gram witness",
                "There exists a real four by four matrix S such that S and S + C are "
                + "positive semidefinite and each has rank at most two, every row sum of S "
                + "is zero, and Sᵢᵢ = qᵢ for every i."),
            Theorem("coupling-diagonal", "coupling_diag", "The second diagonal profile",
                "For bistochastic B and every i, Cᵢᵢ = pᵢ − qᵢ by the column sum equation."),
            Theorem("coupling-row-sum", "coupling_row_sum", "The second Gram also has zero row sums",
                "For bistochastic B and every i, the sum of Cᵢⱼ over j is zero by the row and column sum equations."),
            Theorem("grams-from-unitary", "coupledPlanarGrams_of_unitary", "A unitary supplies the Gram witness",
                "For any unitary U of order four, B = normSqMatrix(U) satisfies CoupledPlanarGrams. "
                + "Take the real Gram matrices of the complex links U₀ⱼ conjugate(U₁ⱼ) and "
                + "U₂ⱼ conjugate(U₃ⱼ). Each link family sums to zero by row orthogonality. "
                + "For distinct columns, column orthogonality makes the partial inner products "
                + "for the two row pairs opposite. Their equal squared moduli give the "
                + "off-diagonal entries of C, and the link moduli give the diagonal."),
            Theorem("unitary-from-grams", "exists_unitary_of_coupledPlanarGrams", "Reconstruction from the common witness",
                "For bistochastic B, CoupledPlanarGrams(B) supplies a unitary U of order four with "
                + "B = normSqMatrix(U). Factor S in the real plane and take its vectors as complex "
                + "links. Their sum has squared norm zero. Realize the links with the first two "
                + "prescribed rows, choosing the second entry freely at a zero first-row weight "
                + "with its prescribed modulus. The resulting orthonormal rows extend to a unitary.",
                "In the complementary rows, the Bloch vectors have Gram matrix ddᵀ + 4(S + C), "
                + "where d = e − f. Factor S + C using two real coordinates and append d as "
                + "the third coordinate after scaling the planar coordinates by two. The resulting "
                + "vectors and the actual Bloch vectors have equal Gram matrices. An ambient "
                + "isometry transports the third unit axis to a unit readout axis with inner "
                + "products dᵢ. A two-row unitary rotation then realizes e, and column normalization "
                + "supplies f. The factorizations and isometry include planar ranks zero, one and two."),
            Theorem("unistochastic-iff-coupled-planar-grams", "unistochastic_iff_coupledPlanarGrams",
                "The coupled planar Gram criterion",
                "Every order-four bistochastic B is unistochastic exactly when CoupledPlanarGrams(B) "
                + "holds. Unistochasticity means there exists a complex unitary U of order four "
                + "with B = RHLinalg.normSqMatrix(U). Zero entries are allowed in every row and column.",
                "Haagerup’s procedure, presented by Rajchel, Gąsiorowski and Życzkowski in "
                + "arXiv:1804.10715v2, Appendix A, Eqs. (7.1)–(7.5), joins the first row and "
                + "column quadrilaterals at a common phase and tests one remaining modulus after "
                + "block completion. The coupled Gram criterion expresses the shared compatibility "
                + "through two planar Gram matrices and reconstructs the last row pair by an "
                + "isometry in the Bloch coordinates."),
            Definition("third-off-diagonal", "thirdOffdiag", "The third off-diagonal",
                "For real x and y, set z = (q₃ − q₀ − q₁ − q₂)/2 − x − y. "
                + "For a symmetric S with zero row sums and diagonal q, its leading three "
                + "off-diagonals are x, y, z when S₀₁ = x and S₀₂ = y."),
            Definition("cubic", "cubic", "The first leading determinant",
                "F = q₀q₁q₂ + 2xyz − q₀z² − q₁y² − q₂x² is the determinant of the leading "
                + "three-by-three block of S."),
            Definition("conic", "conic", "The difference of leading determinants",
                "Set A = C₀₁, D = C₀₂ and E = C₁₂. The conic is defined by p₀p₁p₂ − q₀q₁q₂ "
                + "+ 2(Ayz + Dxz + Exy + ADz + AEy + DEx + ADE) − p₀(z + E)² "
                + "− p₁(y + D)² − p₂(x + A)² + q₀z² + q₁y² + q₂x². This is the determinant "
                + "with diagonal p₀, p₁, p₂ and off-diagonals x + A, y + D, z + E, minus F. Since z "
                + "is affine in x and y, the degree in those two variables is at most two."),
            Definition("cubic-conic-feasible", "CubicConicFeasible", "Two equations with six minor inequalities",
                "There are real x and y for which the cubic and conic vanish and "
                + "x² ≤ q₀q₁, y² ≤ q₀q₂, z² ≤ q₁q₂, (x + A)² ≤ p₀p₁, "
                + "(y + D)² ≤ p₀p₂, and (z + E)² ≤ p₁p₂."),
            Theorem("coupled-grams-iff-cubic-conic", "coupledPlanarGrams_iff_cubicConicFeasible",
                "The leading blocks determine the full Grams",
                "For every order-four bistochastic B, the coupled Gram criterion is equivalent "
                + "to the cubic and conic feasibility criterion. With nonnegative diagonals, "
                + "zero determinant and the three principal minors of order two characterize "
                + "positive semidefiniteness and rank at most two in each leading block. "
                + "The proof treats a zero pivot separately. Augmenting the blocks by zero "
                + "row and column sums preserves positivity and the rank bound, and the last "
                + "diagonal entry of S is fixed by the definition of z."),
            Theorem("unistochastic-iff-cubic-conic", "unistochastic_iff_cubicConicFeasible",
                "The guarded cubic and conic criterion",
                "Every order-four bistochastic B is unistochastic exactly when CubicConicFeasible(B) "
                + "holds. The test concerns a common real solution of both equations and all six "
                + "inequalities, including zeros of the weights, singular Gram blocks and "
                + "degenerate conics. It gives a pointwise completion criterion for the "
                + "flat-star-shapedness question, which asks for feasibility at every point "
                + "on each segment from the flat matrix to a unistochastic endpoint."))));

    private static DocumentBlock.Describe Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(
        string id, string name, string title, string text, string? explanation = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(),
            name == "unistochastic_iff_coupledPlanarGrams"
                ? AssessedProvenance.FromRepo(Haagerup) : AssessedProvenance.FromRepo(),
            explanation is null ? Blocks(Paragraph(Text(text))) :
                Blocks(Paragraph(Text(text)), Paragraph(Text(explanation))), DescribeRole.Theorem);
}
