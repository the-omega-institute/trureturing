using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Subentropy;

internal sealed class GaussianQuadraticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hermitian quadratic forms diagonalize in a Gaussian-preserving spectral basis.",
        H("Gaussian quadratic forms"),
        Blocks(
            Describe.Lean(DescribeId.Create("gaussian-quadratic-form"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianQuadratic.gaussianQuadratic"),
                H("The normalized quadratic readout"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("The quadratic readout is one half of the real part of the complex inner product of z with Az, on the complex Euclidean space regarded as a real Gaussian space. In a Hermitian eigenbasis it is one half of the sum of eigenvalue times squared complex coordinate norm. The underlying real linear isometry preserves standard Gaussian measure. Neither identity requires distinct eigenvalues or invertibility.")),
                    Paragraph(Text("Positive semidefinite matrices give nonnegative readouts. If the complement I-A is also positive semidefinite, the readout is at most one half the squared norm of z. These quadratic and measure identities supply spectral transport only; they do not assert the entropy expectation representation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complex-gaussian-coordinates"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianQuadratic.complexGaussianCoordinates"),
                H("Pairing real Gaussian coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("complexGaussianCoordinates pairs each two independent standard real Gaussian coordinates as the real and imaginary parts of one complex coordinate. Its product-Gaussian pushforward is the standard real Gaussian measure on complex Euclidean space. The squared complex coordinate norm is the sum of the squares of its two real coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complex-coordinate-transport"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianQuadratic.complex_coordinate_transport"),
                H("The real-coordinate Gaussian law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("Pairing independent real standard Gaussian coordinates gives standard Gaussian measure on complex Euclidean space. Each squared complex coordinate norm is exactly the sum of the squares of its two real components. The proof uses the real orthonormal basis consisting of the coordinate vectors and their multiples by the imaginary unit."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("spectral-quadratic-transport"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianQuadratic.spectral_transport"),
                H("Gaussian-preserving spectral transport"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("The inverse eigenbasis coordinate map of a Hermitian matrix preserves standard Gaussian measure. At every coordinate vector w, the quadratic readout after this map is one half of the sum of lambda_i times normSq(w_i). Zero and repeated eigenvalues are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gaussian-quadratic-nonnegative"),
                DeclarationHandle.Create("D5/S3/Quantum/Subentropy/GaussianQuadratic.quadratic_nonnegative"),
                H("Positive quadratic readouts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Entropy/datta2014subentropy")),
                Blocks(
                    Paragraph(Text("For a positive semidefinite complex matrix A, gaussianQuadratic A z is nonnegative at every Euclidean vector z. This is the positive-semidefinite quadratic-form law with the positive normalization factor one half."))), DescribeRole.Theorem))));
}
