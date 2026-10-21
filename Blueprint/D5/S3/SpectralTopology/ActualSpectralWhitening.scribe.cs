using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class ActualSpectralWhiteningDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual spectral smoothness used in the original reversible-channel application. The cited channel literature supplies context. The analytic proof identifies the actual CFC square root with a local inverse of the Hermitian square map.",
        H("Actual spectral whitening"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-hermitian-sqrt-cont-diff-at"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/ActualSpectralWhitening.positive_hermitian_sqrt_contDiffAt"),
                H("positive hermitian sqrt contDiffAt"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("At every positive definite Hermitian matrix, the actual CFC square root is smooth as a map from the real Hermitian subspace to the original complex matrix space. The derivative of the square map at its positive square root is the invertible Jordan operator V \u21a6 YV + VY. The local inverse theorem gives a smooth local inverse; uniqueness identifies that inverse with the CFC square root."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("support-range"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/ActualSpectralWhitening.support_range"),
                H("support range"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("For every positive semidefinite complex matrix, the actual spectral support has the same complex linear range as the matrix, is Hermitian and is idempotent. The proof uses CFC multiplication and the zero-on-kernel support function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-constant-rank-support-smooth"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_support_smooth"),
                H("actual constant rank support smooth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("For an arbitrary smooth family of positive semidefinite complex matrices on an arbitrary real manifold with fixed original model with corners and constant natural rank, the actual spectral support varies smoothly. Locally, an independent family of actual columns gives the Gram projection C(C* C)\u207b\u00b9C*. Its range and orthogonal-projection identities identify it with spectralSupport. Rank zero and empty bases are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-matrix-sqrt-smooth"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/ActualSpectralWhitening.positive_matrix_sqrt_smooth"),
                H("positive matrix sqrt smooth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("Every smooth family of positive definite complex matrices has a smooth actual CFC square root. Projection to the real Hermitian subspace and the positive square-root local-inverse theorem give smoothness at every base point. No differentiable spectral decomposition or extra regularity premise is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-whitening-extension"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/ActualSpectralWhitening.actual_whitening_extension"),
                H("actual whitening extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("For a positive semidefinite matrix Q, write P = spectralSupport(Q) and H = Q + identity \u2212 P. The matrix H is positive definite. The original zero-on-kernel inverse square root is P(sqrt(H))\u207b\u00b9, and the original CFC square root is P sqrt(H). Scalar spectral identities, transported through the actual CFC, prove both equalities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-constant-rank-whitening-smooth"),
                DeclarationHandle.Create("D5/S3/SpectralTopology/ActualSpectralWhitening.actual_constant_rank_whitening_smooth"),
                H("actual constant rank whitening smooth"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("For every smooth constant-rank positive semidefinite matrix family, its actual support, zero-on-kernel inverse square root, and CFC square root are smooth on the original manifold. Local Gram coordinates give the smooth support; the extension H = Q + identity \u2212 P is smooth and positive definite. Composing the actual positive square root with matrix inversion and multiplication gives both spectral functions. The live local-inverse identification is reused by this endpoint. All dimensions and ranks remain arbitrary natural numbers, including zero."))),
                DescribeRole.Theorem))));
}
