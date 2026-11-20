using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleRemaining;

internal sealed class HalfBothCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Half-step polynomial certificates: HalfBothCertificates",
        H("Six corners for one dyadic parameter region"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-half-both-certificates-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfBothCertificates.half_both2_negative"),
                H("The negative corner"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For K>=2 and F>=2, written K=2+X and F=2+Y, let e=1+Z and t=8*K*F+T, with X,Y,Z,T nonnegative integers. The negative corner has h=0,r=e. Four exact scaled seam margins are proved using explicit sparse polynomials in Horner form, ring normalization and positivity."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-half-both-certificates-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleRemaining/HalfBothCertificates.half_both2_boundary"),
                H("Positive corners and the boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same source module supplies half_both2_p11, half_both2_p1r, half_both2_ph1 and half_both2_phr for the four corners h=1 or 2K and r=1 or 2Fe, plus half_both2_boundary for the separate t=4KF rectangle case. Six charts contribute 24 margins in this parameter region. HalfStep.half_corners consumes them before affine interpolation and native conversion. These are sufficient arithmetic inequalities; the physical reconstruction is supplied downstream."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
