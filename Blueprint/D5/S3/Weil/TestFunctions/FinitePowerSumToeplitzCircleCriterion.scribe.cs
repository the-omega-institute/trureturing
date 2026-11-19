using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class FinitePowerSumToeplitzCircleCriterionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/TestFunctions/FinitePowerSumToeplitzCircleCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite family closed under inversion in the unit circle lies on the circle exactly when its power-sum Toeplitz matrix is positive semidefinite.",
        H("Toeplitz positivity of power sums and the unit circle"), Blocks(
            Paragraph(Text(
                "Let u be a family of m nonzero complex numbers that is closed, with multiplicities, "
                + "under inversion in the unit circle z ↦ 1/conj(z): there is a permutation σ of the "
                + "indices with u(σ j) = 1/conj(u j). The permutation records the multiplicities; closure "
                + "of the set of values alone is not enough, since for the multiset {2, 1/2, 1/2} the "
                + "power sums give p(−1) = 9/2 while p(1) = 3. The Toeplitz matrix is the matrix "
                + "toeplitzMatrix of LiCurvatureCriterion, whose (j, k) entry for 0 ≤ j, k ≤ N is "
                + "p(j − k).")),
            Definition("finite-toeplitz-power-sum", "Integer power sums", "powerSum",
                "powerSum u k is p(k) = Σ_j u_j^k for an integer k."),
            Describe.Lean(DescribeId.Create("finite-toeplitz-on-circle"),
                DeclarationHandle.Create(Module + "powerSum_toeplitz_posSemidef_of_norm_eq_one"),
                H("A family on the unit circle gives positive semidefinite Toeplitz matrices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite family u with |u_j| = 1 for every j, the (N + 1) × (N + 1) "
                        + "matrix with entries p(j − k) is positive semidefinite for every N. No "
                        + "closure hypothesis and no bound relating N to the size of the family is "
                        + "needed.")),
                    Paragraph(Text(
                        "This is the finite-Dirac-measure case of the circle-moment Toeplitz "
                        + "positivity theorem: when |u_j| = 1 the point 1/u_j lies on the circle and "
                        + "(1/u_j)^(−n) = u_j^n, so p is the moment sequence of the measure "
                        + "Σ_j δ(1/u_j), and the proof applies "),
                        Ref("D5/S3/Weil/TestFunctions/LiCurvatureCriterion.circle_moment_toeplitz_posSemidef"),
                        Text(" to that measure."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-toeplitz-circle-criterion"),
                DeclarationHandle.Create(Module + "toeplitz_posSemidef_iff_norm_eq_one"),
                H("Positive semidefiniteness detects the unit circle"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/QuadraticForms/hermite1856rootcount"),
                    LibraryNoteRef.Create("D5/L/QuadraticForms/kreinnaimark1981hermitianforms"),
                    LibraryNoteRef.Create("D5/L/Weil/simon2005opuc")),
                Blocks(
                    Paragraph(Text(
                        "Let u be nonzero and closed under z ↦ 1/conj(z) with multiplicities, witnessed "
                        + "by σ, and let d be the number of distinct values of u. For every N with "
                        + "d ≤ N + 1, the (N + 1) × (N + 1) matrix with entries p(j − k) is positive "
                        + "semidefinite if and only if |u_j| = 1 for every j. Since d ≤ m, this holds in "
                        + "particular for N = m − 1 and every larger N.")),
                    Paragraph(Text(
                        "Proof: the backward direction is the previous theorem. For the forward "
                        + "direction, for a coefficient vector x with polynomial P(w) = Σ_a x_a w^a, "
                        + "the quadratic form equals Σ_j conj(P(conj u_j)) P(conj u(σ j)), because "
                        + "u_j^(a − b) = u_j^a conj(u(σ j))^b. If some z = u_i has |z| ≠ 1, the points conj(z) and 1/z are "
                        + "distinct nodes among the d values conj(u_j). Lagrange interpolation gives a "
                        + "polynomial of degree below d, hence a coefficient vector of length N + 1, with "
                        + "value 1 at conj(z), value "
                        + "−1 at 1/z and value 0 at the other nodes. Each term of the form is then 0 or "
                        + "−1, and the term with index i is −1, so the form has real part at most −1.")),
                    Paragraph(Text(
                        "Scope: the theorem does not count negative eigenvalues; the inertia statement "
                        + "that the number of negative eigenvalues equals the number of off-circle pairs "
                        + "is not formalized here. The result belongs to the Hermite–Sylvester method of "
                        + "root separation by quadratic and Hermitian forms, surveyed by Krein and "
                        + "Naimark, and to the theory of Toeplitz forms on the unit circle. A verbatim "
                        + "source for this finite-family form was not found; no novelty is claimed, and "
                        + "the repository's contribution is the formal statement and proof."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string title, string declaration, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
