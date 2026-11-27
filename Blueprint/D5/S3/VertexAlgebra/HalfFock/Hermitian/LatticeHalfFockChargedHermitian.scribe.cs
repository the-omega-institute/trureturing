using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock.Hermitian;

internal sealed class LatticeHalfFockChargedHermitianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native Chosen-Tensor Charged Field Hermitian Adjoints",
        H("Native Chosen-Tensor Charged Field Hermitian Adjoints"),
        Blocks(
            Paragraph(Text("The carrier is the literal ActualTensor(D,hu) with its unchanged nested chosen ActualGround, groundRepresentation and groundAction. The form is exactly the original tensorForm. The chargedCoefficient retains chargeScalar(D,a)=2^(-bilinear(D,a,a)), not a modified normalization. Conjugation fixes this real integral power, and replacing a by -a leaves it unchanged. The original chosen-ground signed adjoint is reused with the exact epsilon(D,a,a); group inverse is not silently identified with literal charge reflection.")),
            Describe.Lean(
                DescribeId.Create("charged-coefficient-field-adjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockChargedHermitian.charged_coefficient_field_adjoint"),
                H("Actual Coefficient and Actual Existing Field"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original lattice D, determinant unit proof hu, integral charge a, integer exponent M and arbitrary original tensor states v,w, tensorForm(chargedCoefficient(a,M)v,w) equals epsilon(D,a,a) times tensorForm(v,chargedCoefficient(-a,-M-2*chargeNorm(D,a))w). The theorem also states and proves the same identity for the literal existing chargedField.coeff on all targets and all coefficient exponents. There is no replacement field. On pure tensors, the proved full oscillator coefficient transpose and the original chosen-ground signed adjoint combine with the real chargeScalar. Independent tensor induction in both arguments then proves the law for arbitrary mixed finite tensors, not only separable states. The chargedField clause consumes the resulting operator law through the original HVertexOperator coefficient identity."))),
                DescribeRole.Theorem),
            Paragraph(Text("The theorem gives the adjoint both for the native charged coefficient and for the corresponding coefficient of the original field. The tensor extension uses the original oscillator transpose, the signed ground adjoint and the real charge scalar, which is invariant under charge reflection. The result includes rank zero and indefinite signature wherever the Gram determinant is a unit.")),
            Paragraph(Text("The adjoint concerns the original charged field on the chosen tensor carrier. The all-state twisted Jacobi, gluing and fusion questions remain open.")) )));
}
