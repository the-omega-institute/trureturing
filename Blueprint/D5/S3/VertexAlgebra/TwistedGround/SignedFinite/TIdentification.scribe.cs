using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.SignedFinite;

internal sealed class TIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Finite Gaussian TIdentification", H("Signed Finite Gaussian TIdentification"), Blocks(
            Paragraph(Text("For every e,f:Bool, p,q:Nat and complex z with norm(z)<1, the literal original externalT equals the explicit finite tSigned at z^2. The proof consumes the actual full complex kernel identity, original normal mode sums, the strong original E nonvanishing theorem and finite convolution inversion. No auxiliary equality, summability, radius, regularity or pole premise appears in the endpoint. The wider Monster/VOA/string-theory objective remains open.")),
            Describe.Lean(DescribeId.Create("externalt-signed-finite-eq"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/TIdentification.externalT_signed_finite_eq"), H("externalT_signed_finite_eq"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For every e,f:Bool, p,q:Nat and complex z with norm(z)<1, the literal original externalT equals the explicit finite tSigned at z^2. The proof consumes the actual full complex kernel identity, original normal mode sums, the strong original E nonvanishing theorem and finite convolution inversion. No auxiliary equality, summability, radius, regularity or pole premise appears in the endpoint. The wider Monster/VOA/string-theory objective remains open."))), DescribeRole.Theorem))));
}
