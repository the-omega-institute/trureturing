using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.SignedFinite;

internal sealed class TInverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Finite Gaussian TInverse", H("Signed Finite Gaussian TInverse"), Blocks(
            Paragraph(Text("Scaling the existing unconditional finite h and h2 stencil identities gives inverses of the four actual signed denominators. Every required nonzero scalar follows from norm(r)<1. No norm bound is imposed on the transformed polynomial parameter.")),
            Describe.Lean(DescribeId.Create("stencil-unique"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/TInverse.stencil_unique"), H("stencil_unique"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Scaling the existing unconditional finite h and h2 stencil identities gives inverses of the four actual signed denominators. Every required nonzero scalar follows from norm(r)<1. No norm bound is imposed on the transformed polynomial parameter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mulpoly-epolynomial"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/TInverse.mulPoly_ePolynomial"), H("mulPoly_ePolynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Scaling the existing unconditional finite h and h2 stencil identities gives inverses of the four actual signed denominators. Every required nonzero scalar follows from norm(r)<1. No norm bound is imposed on the transformed polynomial parameter."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("h-stencils"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/SignedFinite/TInverse.H_stencils"), H("H_stencils"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Scaling the existing unconditional finite h and h2 stencil identities gives inverses of the four actual signed denominators. Every required nonzero scalar follows from norm(r)<1. No norm bound is imposed on the transformed polynomial parameter."))), DescribeRole.Theorem))));
}
