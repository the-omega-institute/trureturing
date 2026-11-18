using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.SignedFinite;

internal sealed class PolynomialDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Finite Gaussian Polynomial", H("Signed Finite Gaussian Polynomial"), Blocks(
            Paragraph(Text("Finite polynomial multiplication extracts exactly the guarded coefficient shifts. The polynomial carrier includes u^2 v^2, so the mixed J quartic contribution is retained.")),
            Describe.Lean(DescribeId.Create("jointseries-finsum"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/Polynomial.finSum"), H("JointSeries.finSum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Finite polynomial multiplication extracts exactly the guarded coefficient shifts. The polynomial carrier includes u^2 v^2, so the mixed J quartic contribution is retained."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jointseries-mulpoly"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/Polynomial.polynomial_mul"), H("JointSeries.polynomial_mul"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Finite polynomial multiplication extracts exactly the guarded coefficient shifts. The polynomial carrier includes u^2 v^2, so the mixed J quartic contribution is retained."))), DescribeRole.Theorem))));
}
