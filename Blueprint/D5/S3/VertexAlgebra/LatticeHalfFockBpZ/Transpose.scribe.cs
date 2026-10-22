using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class TransposeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Creation multiplication and the actual translated-polynomial coefficient are bilinear transposes.",
        H("Native Creation Multiplication Transpose"),
        Blocks(Describe.Lean(
            DescribeId.Create("halfcreationmultiplicationtranspose"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Transpose.half_creation_multiplication_transpose"),
            H("Same-Charge Complex-Bilinear Transpose"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For arbitrary original half-Fock polynomials and every integer degree, multiplying the first polynomial by halfCreationCoeff transposes to the corresponding coefficient of halfTranslatedPolynomial applied to the second. The charge is identical on both sides. halfTranslationCoeff extends the original polynomial coefficients by zero at negative integer degrees; it changes neither the polynomial nor its variables.")),
                Paragraph(Text("Polynomial induction uses the exact negative BPZ creator adjoint, the actual current Leibniz rule, and the odd-weight creation derivative. Translation of a creator subtracts the Gram charge pairing times the degree-shifted polynomial. The factor n+1/2 cancels 2/(2n+1), producing precisely this subtraction. The vacuum case follows from the actual bilinear vacuum functional and odd-weight homogeneity.")),
                Paragraph(Text("The result is complex-bilinear, not Hermitian. It is independent of finite-dimensional grade restrictions and is valid for every finite-support polynomial."))),
            DescribeRole.Theorem))));
}
