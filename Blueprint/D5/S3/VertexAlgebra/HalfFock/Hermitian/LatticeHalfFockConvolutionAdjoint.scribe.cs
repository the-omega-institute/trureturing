using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock.Hermitian;

internal sealed class LatticeHalfFockConvolutionAdjointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Half-Fock Oscillator Coefficient Adjoints",
        H("Original Half-Fock Oscillator Coefficient Adjoints"),
        Blocks(
            Paragraph(Text("This proof acts on the literal oscillatorCoefficient in LatticeHalfFockChargedTensorCoefficients. Its summands remain oscillatorTerm(D,a,M,P,d) = coeff(d,halfTranslatedPolynomial(D,a,P)) times halfCreationCoeff(D,a,M+chargeNorm(D,a)+d). The sum is supported in the actual finite support of the translated polynomial. The proof uses the finite support law, the creation recurrence and the original oscillator current Ward identity.")),
            Describe.Lean(
                DescribeId.Create("oscillator-coefficient-adjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockConvolutionAdjoint.oscillator_coefficient_adjoint"),
                H("All Charges, Exponents and Oscillator Pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact reflected charge is -a and the exact reflected exponent is -M-2*chargeNorm(D,a). To derive the index, write A=M+chargeNorm(D,a). The constant coefficient of the original oscillator sum only retains translated degree -A when A is nonpositive. Charge reflection leaves the norm unchanged; hence the reflected total creation index must equal -A, which forces the displayed exponent. The full proof extends the already established creation/translation transpose by structural induction on the complete finite input polynomial P, generalizing the exponent and the entire target Q. In the creation step, the original coefficient creator law shifts M by 2k+1; the actual positive-current Ward law on the reflected target shifts the reflected exponent by -(2k+1). Their equality is proved in integer arithmetic. This maintains normal order without interchanging unrestricted infinite series or imposing an arbitrary cutoff."))),
                DescribeRole.Theorem),
            Paragraph(Text("The transpose holds for arbitrary polynomials and integer exponents, including rank zero and indefinite original Gram matrices. LatticeConvolutionFockAdjoint supplies the prior integer-frequency proof architecture.")) )));
}
