using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.LinGProperty;

internal sealed class ArithmeticBoundDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Matrix/LinGProperty/ArithmeticBound.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arithmetic spectral bound retains the deficit in the normalized block overlap.",
        H("The trace-corrected arithmetic bound"), Blocks(
            Describe.Lean(DescribeId.Create("normalized-arithmetic-bound"),
                DeclarationHandle.Create(Owner + "normalized_arithmetic_bound"),
                H("An indexed arithmetic bound with trace deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
                Blocks(
                    Paragraph(Text("Let [A X; X-adjoint B] be positive semidefinite, with tr A=tr B=1. Every decreasingly ordered singular value satisfies 2 s_j(X) <= lambda_j(A+B)+1-|tr X|. All finite dimensions and singular blocks are included.")),
                    Paragraph(Text("A unit phase makes the trace of X real and nonnegative without changing block positivity or any singular value. The Hermitian dilation [0 X; X-adjoint 0] has leading eigenvalues s_j(X). An explicit similarity from a singular value decomposition proves this identity, while Loewner monotonicity compares twice this dilation with the original positive block matrix.")),
                    Paragraph(Text("Write the positive block matrix as Z Z-adjoint and partition its rows into U and V. Its eigenvalues agree with those of U-adjoint U+V-adjoint V. The latter matrix is one half of the sum Gram plus one half of the difference Gram. A positive matrix is bounded above by its trace times the identity, so the difference Gram contributes exactly 1-Re tr X.")),
                    Paragraph(Text("The leading eigenvalues of rectangular row and column Grams agree after zero padding. Finally, the row sum Gram (U+V)(U+V)-adjoint is bounded above by 2(A+B). Combining these comparisons gives the indexed inequality."))),
                DescribeRole.Theorem),
            Item("trace_identity_sub_posSemidef", "Trace ceiling for a positive matrix",
                "For every finite index type with decidable equality and every positive semidefinite complex square matrix A, "
                + "Re(tr A) I minus A is positive semidefinite. The spectral theorem bounds each nonnegative eigenvalue by their sum."),
            Item("row_gram_sum_comparison", "Row Gram comparison",
                "For finite row and column index types with decidable equality and arbitrary complex matrices U,V of the same rectangular shape, "
                + "2(U U-adjoint+V V-adjoint) minus (U+V)(U+V)-adjoint is positive semidefinite. "
                + "Expanding identifies this matrix with (U-V)(U-V)-adjoint."),
            Item("eigenvalues_zero_eq_of_charpoly", "Ordered spectra from the characteristic polynomial",
                "For Hermitian complex matrices A,B on the same finite index type with decidable equality, equality of their characteristic "
                + "polynomials implies equality of every decreasingly ordered eigenvalue. The index ranges over Fin(cardinality of the index type)."),
            Item("rectangular_gram_eigenvalues", "The leading rectangular Gram spectrum",
                "For every natural n, every complex matrix T with n rows and 2n columns indexed by Fin n plus Fin n, and every j in Fin n, "
                + "the j-th decreasing eigenvalue of T-adjoint T equals the j-th decreasing eigenvalue of T T-adjoint. "
                + "The assertion includes zero eigenvalues and imposes no rank condition."),
            Item("eigenvalues_zero_mono_finite", "Ordered eigenvalues respect positive differences",
                "For Hermitian complex matrices A,B on any finite index type with decidable equality, positivity of B-A implies "
                + "lambda_j(A)<=lambda_j(B) at every decreasingly ordered index. Reindexing transports the established finite-dimensional comparison."),
            Item("eigenvalues_zero_smul_finite", "Nonnegative scalar scaling of the ordered spectrum",
                "For a Hermitian complex matrix A on any finite index type with decidable equality, a nonnegative real r and a Hermitian "
                + "witness for rA, every decreasingly ordered eigenvalue satisfies lambda_j(rA)=r lambda_j(A). "
                + "Zero scaling and empty index types are included."),
            Item("eigenvalues_zero_add_scalar_finite", "Scalar translation of the ordered spectrum",
                "For a Hermitian complex matrix A on any finite index type with decidable equality, any real r and a Hermitian "
                + "witness for A+rI, every decreasingly ordered eigenvalue satisfies lambda_j(A+rI)=lambda_j(A)+r."),
            Item("dilation_eigenvalues", "The leading Hermitian dilation spectrum",
                "For every natural n, every complex n by n matrix X and a Hermitian witness for the block matrix [0 X; X-adjoint 0], "
                + "its first n decreasingly ordered eigenvalues are the decreasingly ordered singular values of X. "
                + "A singular value decomposition and zero-aware ordering identify the entire leading spectrum."))));

    private static DocumentBlock Item(string name, string title, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/lin2016gproperty")),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
