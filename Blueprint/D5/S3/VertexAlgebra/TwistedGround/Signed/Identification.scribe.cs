using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.Signed;

internal sealed class IdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Signed Gaussian Identification",
        H("Original Signed Gaussian Identification"),
        Blocks(
            Paragraph(Text("Let r be real with 0<r<1 and let norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1. In each sector with at least one negative label, the original J and T generators equal their explicit signed analytic candidates. The proof subtracts the exact spatial equations, including the J constant, obtains genuine joint differentiability from the original bilinear resolvent and candidate analyticity, and applies spatial uniqueness on radius 1-sqrt(r). This result concerns real radial r; extension to arbitrary complex source parameters requires analytic continuation.")),
            Describe.Lean(DescribeId.Create("signedj-eq-candidatej"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedJ_eq_candidateJ"), H("signedJ_eq_candidateJ"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For either pair e,f of Boolean labels with e=false or f=false, the original kernelMode(false,e,f,u,v,sqrt(r)) equals candidateJ(e,f,u,v,r), for every real 0<r<1 and complex u,v satisfying the original source bidisk bounds. There are no additional source, regularity, equality, boundary or nonzero-denominator assumptions."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signedt-eq-candidatet"), DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/Signed/Identification.signedT_eq_candidateT"), H("signedT_eq_candidateT"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For either pair e,f of Boolean labels with e=false or f=false, the original kernelMode(true,e,f,u,v,sqrt(r)) equals candidateT(e,f,u,v,r), for every real 0<r<1 and complex u,v satisfying the original source bidisk bounds. The conclusion includes both axes, the origin and the diagonal."))), DescribeRole.Theorem)
        )));
}
