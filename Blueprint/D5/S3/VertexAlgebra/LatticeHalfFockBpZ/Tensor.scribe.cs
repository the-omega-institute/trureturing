using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockBpZ;

internal sealed class TensorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual chosen Leech half-Fock tensor carries a symmetric complex-bilinear pairing with both radicals zero.",
        H("BPZ Pairing on the Original Leech Tensor"),
        Blocks(Describe.Lean(
            DescribeId.Create("tensorpairingnondegenerate"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockBpZ/Tensor.tensor_pairing_nondegenerate"),
            H("Both Tensor Radicals Vanish"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("tensorPairing is the tensor product of oscillatorPairing and the existing NativeSymmetricForm.nativePairing. Its carrier is ActualTensor of ExplicitLeechLattice.data with the original nested chosen ground. On pure tensors it is the product of the two complex-bilinear pairings. The ground form, its actual orbit basis, its symmetry and its exact integral cocycle adjoint are reused, not replaced by an assumed representation equivalence.")),
                Paragraph(Text("The original native ground basis identifies a tensor with finitely supported polynomial coordinates. Pairing against a polynomial tensored with one ground basis vector extracts exactly the oscillator pairing of that coordinate. A radical tensor therefore has every coordinate zero. Symmetry supplies the other radical. The native tensor current reflects index j to -j-1 with a minus sign. The existing NativeSymmetricForm.original_integral_adjoint retains epsilon(a,-a) and groundAction(-a); it is a reused supplier result, not a new tensor theorem.")),
                Paragraph(Text("The charged oscillator coefficient transpose remains unproved: oscillatorPairing(data)(oscillatorCoefficient(data,a,e)(p),q) = oscillatorPairing(data)(p,oscillatorCoefficient(data,a,-2*chargeNorm(data,a)-e)(q)). Its proof must relate the actual creation exponential and translated-polynomial coefficients and justify the finite-sum reindexing. Together with the reused ground adjoint it would give the original charged tensor adjoint retaining chargeScalar(data,a), epsilon(data,a,-a), the same oscillator charge a and the original ground action at -a. No charged-field or all-state BPZ invariance is asserted here."))),
            DescribeRole.Theorem))));
}
