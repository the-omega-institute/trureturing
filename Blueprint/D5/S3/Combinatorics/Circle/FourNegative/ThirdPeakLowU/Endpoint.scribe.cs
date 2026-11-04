using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU;
internal sealed class EndpointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Third peak low U: unbounded original physical constructions",
        H("Strict 2<=a<b<d, d+3<=c; fallback (2,3,d+2,d), d>=4"),
        Blocks(
            Describe.Lean(DescribeId.Create("thirdpeaklowu-strict-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Endpoint.actualSource_third_peak_low_u_strict_joint_lift"),
                H("Every strict original source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural 2<=a<b<d and d+3<=c, let k=a+b+c+d and seed=1+2^a+2^(a+b)+2^(a+b+c). A permutation sigma of the original Fin k labels and a cut j<=k satisfy OriginalOrder for this seed, and earWord inserts the literal fresh label k to satisfy OriginalOrder for the doubled seed on Fin (k+1). Both scalar rows satisfy their original prefix bounds for every natural repetition count and every take length, including zero and overlong takes. The old and new repeated totals vanish separately.")),
                    Paragraph(Text("The U mask is 2^(d-b)-1; b+1=d remains in the domain. A positive integer ceiling selects the V coefficient. The W coefficient uses the two adjacent dyadic ratios or an exact integer quotient. Shifted nonnegative polynomial identities and quotient-remainder inequalities prove the six actual residual bounds."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("thirdpeaklowu-fallback-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Endpoint.actualSource_third_peak_low_u_fallback_joint_lift"),
                H("Every original fallback source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural d>=4 the same conclusions hold for (a,b,c,d)=(2,3,d+2,d), k=2+3+(d+2)+d, and the unchanged original seed 1+2^2+2^(2+3)+2^(2+3+(d+2)). The residue selector uses s=2^(d-3), A=1024s+37, and SU=592s+1, selecting r=s or r=s-1 by the actual remainder interval. The case d=4 is retained, and all larger powers are handled without a finite positive table.")),
                    Paragraph(Text("Both families retain packet order V,W,X,U. Complementary chamberLabels partition the literal original label banks. The fresh ear is in packet slot one, after its positive packet and immediately before the W negative label. Native packet masses and terminal values give post-negative residuals L-vB; K-wL+uA-vB; (u+1)A-vB; SV-vSU; SW-wSV+(2u+1)A-vSU; and (2u+2)A-vSU, with doubled caps L-1,K-1,A-1,SV-1,SW-1,A-1. The third new cap uses A, the actual next head after the X negative label.")),
                    Paragraph(Text("These are applications and kernel integrations of the supplied physical constructions. Literature novelty, official delivery, and a solution of the unrestricted Circle problem are not claimed."))), DescribeRole.Theorem)), []));
}
