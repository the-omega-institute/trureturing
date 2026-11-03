using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalFourMInputsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original lattice twisted-sector coefficient reduction, preserving the original carriers and operators.",
        H("OriginalFourMInputs"),
        Blocks(
            Describe.Lean(DescribeId.Create("originalfourminputs-tensor-input-energy"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.tensor_input_energy"),
                H("Compatible original polynomial tensors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("An original polynomial P has sigma P=-P and signed odd weighted degree 2H-3. Every selected ActualGround vector x gives tensorInput with underlying vector P tensor x in the original paritySpace(-1). Its actualTensorL0 eigenvalue is H. The proof uses the original zero-mode theorem, whose constant shift is rank/16; rank 24 makes the oscillator half-energy H-3/2. Zero polynomials and zero ground vectors remain allowed."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalfourminputs-input-trilinear-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_expansion"),
                H("Finite expansion of all three inputs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every complex trilinear map on the original negative-parity tensor module and every original u,v,w, expand each input using MixedJacobiFinite.actual_input_basis_expansion through legal OpenPrivate. The three sums run over the attached actual finite coordinate supports, with the product of their actual basis coefficients. Finite map and scalar distribution commute these sums."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("originalfourminputs-input-trilinear-ext"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalFourMInputs.input_trilinear_ext"),
                H("Homogeneous tensors suffice for an all-input trilinear law"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The actual_input_basis_energy theorem and negative_support identify every term of the preceding expansion with a compatible homogeneous polynomial tensor. Thus zero on all these original tensors implies zero on every original input. This neither changes the carrier to a chosen basis nor assumes extension from the vacuum."))
                ), DescribeRole.Theorem)
        ), []));
}
