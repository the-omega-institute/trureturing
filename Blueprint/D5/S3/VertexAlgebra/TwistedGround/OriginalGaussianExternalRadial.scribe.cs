using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalRadialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Differentiation of the Original External Vectors",
        H("Differentiation of the Original External Vectors"),
        Blocks(
            Paragraph(Text("Polynomial-geometric bounds justify differentiating the complete Hilbert-space external series. The radial derivative is obtained by the real square-root chain rule at positive r, not by changing the original series.")),
            Describe.Lean(
                DescribeId.Create("externalderivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.externalDerivative"),
                H("externalDerivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative vector is the termwise differentiated original external-column Hilbert series, with coefficient (n+1) z^n."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hasderivat-externalvector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_externalVector"),
                H("hasDerivAt_externalVector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either label, every natural p and complex norm(z)<1, externalVector has the complex derivative externalDerivative."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasderivat-radial-externalvector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalRadial.hasDerivAt_radial_externalVector"),
                H("hasDerivAt_radial_externalVector"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all signed modes and real 0<r<1, the real derivative of externalVector at sqrt(r) is frequencyVector divided by 2r."))), DescribeRole.Theorem))));
}
