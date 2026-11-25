using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.HalfFock.Hermitian;

internal sealed class LatticeHalfFockTensorHermitianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal Chosen-Ground Half-Fock Tensor Geometry",
        H("Literal Chosen-Ground Half-Fock Tensor Geometry"),
        Blocks(Paragraph(Text("The carrier is literally ActualTensor(D,hu)=Oscillator(D) tensor ActualGround(D,hu). The exact groundRank and groundRepresentation use the original nested classical choices; no alternative orthonormal representation or equality of an unrelated witness is assumed. For each canonical reduced charge v and original finite ground coordinate t, a proved tensor linear map C(v,t) sends P tensor x to (A_v x)(t) P. The form is the inverse cardinality times the complete finite sum of halfForm(C(v,t)left,C(v,t)right). Its pure tensor formula is exactly halfForm(P,Q) times the existing chargeForm(D,rho)(x,y). This reuses the original charge average and its signed charge geometry, not a new ground averaging theorem. TensorProduct.lift and linear tensor induction follow the existing LatticeBcGhostHermitianForm architecture.")),
            Describe.Lean(
                DescribeId.Create("coordinate-reconstruction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian.coordinate_reconstruction"),
                H("Every Finite Tensor Is Reconstructed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The entire tensor is the finite sum of C(0,t)(state) tensor the literal coordinate basis vector. A_0 is the actual identity. This proves joint injectivity of the zero-charge coordinates on all tensors. The ground coordinate type remains nonempty when groundRank is zero. There is no global tensor occupation cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensorform-positive"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian.tensorForm_positive"),
                H("Strict Positivity on Every Nonzero Tensor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Every diagonal coordinate summand has nonnegative real part under actual gramReal(D) PosDef. Reconstruction forces a nonzero zero-charge coordinate for any nonzero tensor; that summand is strictly positive by the original Fock positivity supplier and the proved invertible half scaling. The complete canonical charge cardinality is positive. Thus positivity is proved for arbitrary finite tensors, not just pure tensors. Hermitian symmetry and zero imaginary diagonal are also proved."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensorform-nondegenerate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian.tensorForm_nondegenerate"),
                H("Both Tensor Radicals Vanish"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("With both original inverse-Gram equations, the half oscillator form is nondegenerate. The original positive ground form gives an injective finite-dimensional coordinate metric map. Mathlib supplies its bijectivity. Testing an arbitrary tensor against all polynomial tensor coordinate vectors, then applying reconstruction and the metric inverse, proves both radicals vanish. No indefinite oscillator positivity is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tensor-ground-signed-adjoint"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockTensorHermitian.tensor_ground_signed_adjoint"),
                H("Original Cocycle-Signed Native Charge Consumer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("On the full tensor, the adjoint of the original groundAction(a) is epsilon(a,a) times groundAction(-a). The coefficient remains paritySign(B(a,a)/2), as supplied by the original native signed adjoint; reflection alone is not the group inverse. The actual original quotient action also preserves the full tensor form. The actual tensorCurrent has the same -j-1 adjoint as the original oscillator current."))),
                DescribeRole.Theorem),
            Paragraph(Text("This is classical algebraic Fock and finite-group Hermitian geometry, not a claim of new physics or literature novelty. It does not establish all-state charged BPZ/PCT or unitarity, a full twisted Jacobi identity, intertwiners, fusion, orbifold gluing, the Monster, a complete string theory or AdS/CFT reconstruction. The full original objective remains open. No all-charge Lorentzian or neutral BRST positivity follows.")))));
}
