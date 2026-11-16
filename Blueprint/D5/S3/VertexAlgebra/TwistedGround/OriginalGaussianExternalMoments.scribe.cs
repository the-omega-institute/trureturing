using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit Source Moments in Displacement",
        H("Explicit Source Moments in Displacement"),
        Blocks(
            Paragraph(Text("U and V are the convergent original shifted-central and centralColumnJet pairings. The public radial inverse-column formulas fix their signs and the square-root factor; these are actual source contractions.")),
            Describe.Lean(
                DescribeId.Create("sourcemoment"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment"),
                H("sourceMoment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("U is the shifted sum over n>=0 of (n+1)(-1)^(n+1) choose(alpha,n+1) x^(n+1) C_(n+1)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sourcejetmoment"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceJetMoment"),
                H("sourceJetMoment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("V is the shifted sum over n>=0 of (-1)^(n+1) choose(alpha,n+1) x^(n+1) H_(n+1), with the original centralColumnJet H."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sourcemoment-eq-modefrequency"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.sourceMoment_eq_modeFrequency"),
                H("sourceMoment_eq_modeFrequency"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed mode and norm(x)<1, U equals the signed mode frequency of A. The constant internal frequency cancels."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-moment-pairings"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.source_moment_pairings"),
                H("source_moment_pairings"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every signed mode and real 0<r<1, pairing its actual external vector with Rminus w gives -sqrt(1-r) U, and pairing with Rplus w gives -sqrt(1-r) V."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("external-displacement-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalMoments.external_displacement_explicit"),
                H("external_displacement_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all signed modes and 0<r<1, the actual J frequency sum equals (1-r)(U_p V_q+V_p U_q)/2, while the actual T frequency difference equals (1-r)(U_p V_q-V_p U_q)/2."))), DescribeRole.Theorem))));
}
