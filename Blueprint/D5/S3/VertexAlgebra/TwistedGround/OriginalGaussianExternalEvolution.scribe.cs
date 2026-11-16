using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalEvolutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full Literal T Radial Evolution and Input Boundary",
        H("Full Literal T Radial Evolution and Input Boundary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("square-half"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.square_half"),
                H("square_half"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex z with norm(z)<1, the actual squareResolvent is one half of the sum of the original resolvent and oppositeResolvent."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("opposite-bilinear-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.opposite_bilinear_transpose"),
                H("opposite_bilinear_transpose"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex z with norm(z)<1 and original Hilbert vectors x,y, the oppositeResolvent has ordinary complex bilinear transpose symmetry, with no Hermitian substitution."))), DescribeRole.Theorem),
            Paragraph(Text("The square resolvent is half the sum of the two actual signed inverses. Its derivative uses the original rank-one operator derivative and ordinary bilinear transpose. The full externalT includes its identity contribution.")),
            Describe.Lean(
                DescribeId.Create("externalt-radial-equation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.externalT_radial_equation"),
                H("externalT_radial_equation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all signed modes and real 0<r<1, the derivative of the actual T at sqrt(r) is the sum of its two mode frequencies plus (1-r)(V_p V_q-U_p U_q)/2, all divided by 2r."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-negative-zero-boundary"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEvolution.external_negative_zero_boundary"),
                H("external_negative_zero_boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either remaining sign and mode and 0<r<1, the literal negative-zero J row is sqrt(1-r)(V-U)/2 and the literal negative-zero T row is sqrt(1-r)(V+U)/2. Both follow from v(-,0)=-w."))), DescribeRole.Theorem))));
}
