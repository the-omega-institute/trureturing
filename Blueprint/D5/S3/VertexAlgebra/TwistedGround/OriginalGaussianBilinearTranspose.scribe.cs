using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianBilinearTransposeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary Bilinear Transpose of the Original Gaussian",
        H("Ordinary Bilinear Transpose of the Original Gaussian"),
        Blocks(
            Paragraph(Text("The pairing is the ordinary complex bilinear sum, implemented by innerSL with star in the first slot. The literal symmetric kernel passes through the norm-absolutely summable rank-one operator series using continuous linear maps and product-index interchange. The actual Neumann inverse inherits this transpose from its geometric inverse identity.")),
            Describe.Lean(
                DescribeId.Create("sourcebilinearfunctional-comm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.sourceBilinearFunctional_comm"),
                H("sourceBilinearFunctional_comm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all square-summable complex vectors x and y, the ordinary source bilinear functional is symmetric."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("operator-bilinear-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.operator_bilinear_transpose"),
                H("operator_bilinear_transpose"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex z of norm less than one and all square-summable x and y, B(x,K(z)y)=B(K(z)x,y)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("resolvent-bilinear-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianBilinearTranspose.resolvent_bilinear_transpose"),
                H("resolvent_bilinear_transpose"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex z of norm less than one and all square-summable x and y, B(x,R(z)y)=B(R(z)x,y), where R is the actual signed Neumann inverse of one minus K."))), DescribeRole.Theorem))));
}
