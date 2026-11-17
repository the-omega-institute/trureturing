using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianSourceDerivativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Radial Derivative of the Literal Original Source Constant",
        H("Radial Derivative of the Literal Original Source Constant"),
        Blocks(
            Paragraph(Text("The real derivative of the source-column pairing is computed using the existing vector derivatives, the ordinary bilinear transpose, the scaled radial column derivative and the exact pair normalization. Real differentiation of star and the inner product retains all conjugations correctly. Eventual equality with source_pairings_explicit transfers the result to the literal sourceConstant series, including its inverse-frequency factor.")),
            Describe.Lean(
                DescribeId.Create("hasderivat-radial-source-pairing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_source_pairing"),
                H("hasDerivAt_radial_source_pairing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r strictly between zero and one, the real radial source-column pairing has complex derivative equal to the real coefficient (1/((1-r)F(r)^2)-1)/(2r)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasderivat-radial-sourceconstant"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceDerivative.hasDerivAt_radial_sourceConstant"),
                H("hasDerivAt_radial_sourceConstant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r strictly between zero and one, u mapped to sourceConstant(sqrt(u)) has complex derivative equal to the embedded real coefficient (1/((1-r)F(r)^2)-1)/(2r)."))), DescribeRole.Theorem))));
}
