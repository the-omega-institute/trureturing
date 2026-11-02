using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalFourMChargeCosetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original lattice twisted-sector coefficient reduction, preserving the original carriers and operators.",
        H("OriginalFourMChargeCoset"),
        Blocks(
            Describe.Lean(DescribeId.Create("originalfourmchargecoset-corrected-tmul"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.corrected_tmul"),
                H("Statewise oscillator factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("All original source charges, source polynomials, integer doubled exponents, oscillator inputs and selected ground vectors occur. Normal-order recursion retains e+2m+2r+3 and both ordering branches; Corr is the original finite correction with e+2s. Mode sums are finite after application to an input, proved by projecting a genuine actual tensor coefficient along an inverse charged ground action. No endomorphism-valued infinite sum is asserted."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalfourmchargecoset-ground-exchange-first"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.ground_exchange_first"),
                H("Original ground Fourier exchange"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The selected ground pairing and the actual charge representation give the exact quadratic and bilinear Fourier signs. Ground completeness consumes OperatorAlgebra.actual_operator_algebra and its reconstruction of rank-one endomorphisms. No ground-basis or reconstruction hypothesis is added."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalfourmchargecoset-fourm-factorization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.fourM_factorization"),
                H("Signed full-energy-fiber coset factorization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The original global inverse I is paired in the first detector slot. The sum ranges over every signed EnergyFiber element, with its original dual inverse-Gram polynomial and occupation factorials. Both chargeScalar factors and exactly one theta half-average remain. Actual homogeneous u,v are polynomial tensors, the third tensor and the detector are unrestricted, and both mode indices are integers."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalfourmchargecoset-original-jacobi-tensor-kernel"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.original_jacobi_tensor_kernel"),
                H("The original scalar detector reduction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every integer m,n,r, use the three sharp finite j cutoffs and common ell output-weight cutoff. Recover all actual detectors by tensor induction. The below-two branch follows the original exact zero and cutoff facts. This statement concerns tensor inputs; the all-input extension is proved separately in OriginalFourMReduction."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalfourmchargecoset-coset-ground-elimination"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMChargeCoset.coset_ground_elimination"),
                H("Independent ground tensors eliminate the four ground variables"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The two Fourier exchanges and independence in the accepted actual operator basis identify the common-channel coefficients. The original ground dimension is 2^12; the Fourier coefficient is its inverse 2^-12. identityK is the explicit channelA/B/D identity built from cosetKernel. It is not defined as Jacobi and is not proved here."))
                ), DescribeRole.Theorem)
        ), []));
}
