using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMDiagonalStabilityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMDiagonalStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace preservation, positivity and log-conditioned trace-norm stability for diagonal BKM recovery.",
        H("Stability of diagonal BKM recovery"),
        Blocks(
            Entry("diagonal-recovery", "diagonalRecovery", "Actual BKM recovery on the diagonal algebra",
                "Fix the coordinate diagonal of a finite complex matrix algebra. For a positive definite "
                + "reference a and diagonal B, divide each B_ii by a_ii and apply the BKM power integral "
                + "Omega_a to the resulting diagonal matrix.", DescribeRole.Definition),
            Entry("diagonal-inverse", "diagonalOmegaInverse_spec", "Two-sided inverse on the diagonal algebra",
                "For every positive definite a, Omega_diag(a) multiplies the i-th diagonal entry by a_ii. "
                + "Coordinate division gives both inverse identities on every complex diagonal B.",
                DescribeRole.Theorem),
            Entry("diagonal-trace", "diagonalRecovery_trace", "Complex trace preservation",
                "For a positive definite reference a and any complex diagonal input B, the trace of "
                + "recovery equals the trace of B. The trace of Omega_a(C) equals the trace of aC, "
                + "and multiplication by a cancels the diagonal division inside the trace.",
                DescribeRole.Theorem),
            Entry("diagonal-tests", "DiagonalTest", "Diagonal density matrices",
                "The tests are all diagonal positive semidefinite matrices of ordinary trace one, "
                + "including singular matrices.", DescribeRole.Definition),
            Entry("spectral-negative-trace", "diagonalRecovery_negativeTrace_eq_spectral", "Negative spectral mass",
                "For a positive definite reference and any diagonal test, recovery produces a Hermitian "
                + "matrix. Half the difference between its trace norm and real trace equals the sum "
                + "of the magnitudes of its negative eigenvalues.", DescribeRole.Theorem),
            Entry("recovery-defect", "diagonalRecoveryDefect", "Defect over diagonal tests",
                "The recovery defect is the supremum of the negative spectral mass over the diagonal "
                + "density matrices.", DescribeRole.Definition),
            Entry("attainment", "diagonalRecoveryDefect_isGreatest", "Rank-one attainment",
                "In nonzero finite dimension, for every positive definite a, one coordinate projector "
                + "of rank one attains the greatest negative spectral mass. Each diagonal test is a "
                + "convex combination of these projectors. Linearity of recovery and convexity of the "
                + "negative trace formula bound its defect by the largest coordinate value.",
                DescribeRole.Theorem),
            Entry("capped-stability", "actual_maximal_abelian_bkm_stability", "Capped log-conditioned estimate",
                "Let a be a positive definite trace-one matrix on any nonempty finite index type. Write "
                + "d for its dimension, X for d times a, and T for the logarithm of the ratio of the largest "
                + "to the smallest eigenvalue of X. With epsilon the recovery defect of a, the unhalved "
                + "trace norm of a minus diag(X)/d is at most the minimum of 2 and "
                + "sqrt((12 + T^2) epsilon (1 + epsilon)). Dimension one and repeated eigenvalues are "
                + "included. The logarithmic mean estimate controls spectral variance through each "
                + "coordinate output's negative trace, and weighted column bounds give the trace norm. "
                + "The cap follows from the unit traces of a and its diagonal.",
                DescribeRole.Theorem),
            Entry("diagonal-positivity", "diagonalRecovery_positive_iff", "Positivity characterizes diagonal references",
                "For a positive definite trace-one reference on a nonempty finite index type, all diagonal "
                + "density matrices have positive semidefinite recovered outputs exactly when a is diagonal. "
                + "Positivity forces zero defect, and stability and trace-norm faithfulness force a to equal "
                + "its diagonal. For a diagonal reference the inverse identity fixes each diagonal input.",
                DescribeRole.Theorem))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
