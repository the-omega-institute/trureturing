using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining;

internal sealed class HalfK4CertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-step polynomial certificates: HalfK4Certificates",
        H("Six corners for one dyadic parameter region"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-half-k4-certificates-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfK4Certificates.half_K4_negative"),
                H("The negative corner"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For K>=4 and F>=1, written K=4+X and F=1+Y, let e=1+Z and t=8*K*F+T, with X,Y,Z,T nonnegative integers. The negative corner has h=0,r=e. Four exact scaled seam margins are proved using explicit sparse polynomials in Horner form, ring normalization and positivity."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-half-k4-certificates-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfK4Certificates.half_K4_boundary"),
                H("Positive corners and the boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same source module supplies half_K4_p11, half_K4_p1r, half_K4_ph1 and half_K4_phr for the four corners h=1 or 2K and r=1 or 2Fe, plus half_K4_boundary for the separate t=4KF rectangle case. Six charts contribute 24 margins in this parameter region. HalfStep.half_corners consumes them before affine interpolation and native conversion. These are sufficient arithmetic inequalities; the physical reconstruction is supplied downstream."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
