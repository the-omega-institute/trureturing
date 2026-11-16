using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteHermitianTraceDualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The trace norm is controlled by Hermitian operator contractions without a dimension factor. For a Hermitian matrix the optimal test is attained. For an arbitrary complex matrix the real and imaginary parts of a maximizing unitary give a bound with factor two. Empty coordinate types are included.",
        H("Hermitian trace tests"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exists-hermitian-tracenorm-test"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.exists_hermitian_traceNorm_test"),
                H("An attaining Hermitian test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite Hermitian complex matrix X there is a Hermitian F of operator norm at most one whose real trace pairing with X equals the trace norm of X. The construction takes the real part of a maximizing unitary; the imaginary part contributes zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hermitian-tracenorm-le-tests"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.hermitian_traceNorm_le_tests"),
                H("Hermitian dual bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A bound m on the real trace pairing with every Hermitian contraction bounds the trace norm of a Hermitian X by m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complex-tracenorm-le-twice-tests"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality.complex_traceNorm_le_twice_tests"),
                H("Complex dual bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For an arbitrary complex X, a bound m on the modulus of its trace pairing with every Hermitian contraction implies traceNorm(X) at most 2m. Both real and imaginary components of the maximizing unitary are used, so the factor two is retained."))),
                DescribeRole.Theorem))));
}
