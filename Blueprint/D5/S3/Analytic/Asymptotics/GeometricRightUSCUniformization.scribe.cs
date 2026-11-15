using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Asymptotics;

internal sealed class GeometricRightUSCUniformizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonmeagre geometric sampling gives a uniform real tail lower bound",
        H("Right upper semicontinuous geometric uniformization"),
        Blocks(Describe.Lean(
            DescribeId.Create("nonmeagre-geometric-right-usc-uniformization"),
            DeclarationHandle.Create("D5/S3/Analytic/Asymptotics/GeometricRightUSCUniformization.uniform_lower_bound_of_nonmeagre_geometric_bases_right_usc"),
            H("Arbitrary real functions and nonmeagre sets of bases"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let F be any real function and T>=1. At each x>=T assume only "
                    + "UpperSemicontinuousWithinAt F (Ioi x) x. Let 1<a<b and let S be an "
                    + "arbitrary nonmeagre subset of (a,b). For each q in S suppose there are "
                    + "its own M>=0 and natural N>=1 such that F(q^k)>=-M for every k>=N. "
                    + "Then one M>=0 and one real X>T satisfy F(x)>=-M for every real x>=X. "
                    + "No measurability, Baire property, continuity on an exceptional-set "
                    + "complement, or common initial sample bound is required.")),
                Paragraph(Text("Round the individual bounds up to integers and cover S by "
                    + "countably many good-base sets. Nonmeagreness forces one ambient "
                    + "closure to have interior. In a smaller open interval, good bases "
                    + "approach each point from the right. Right upper semicontinuity "
                    + "transfers the fixed late-exponent bound to every base there. For "
                    + "1<c<d in that interval, the power bands [c^k,d^k] eventually overlap. "
                    + "Taking a positive real kth root places every sufficiently large "
                    + "real x in a band, giving the full closed final ray.")),
                Paragraph(Text("For an arbitrary sequence u, the step function F(x)=u(floor(x)) "
                    + "is constant on a short right neighborhood, including integer points. "
                    + "If u has no eventual lower bound, applying the theorem on countably "
                    + "many rational base intervals shows that its successful floor-geometric "
                    + "sampling bases form a meagre subset of (1,infinity). A residual set "
                    + "contains an ambient dense G_delta; intersecting it with (1,infinity) "
                    + "gives relative density and a meagre relative complement.")),
                Paragraph(Text("The polynomial canonical Robin criterion supplies the exact "
                    + "sequence u(j)=(j^r)^alpha*log(j^r)*robinLogMargin("
                    + "strictInteger(firstLayerPrice(j^r+1))). Intersect the residual "
                    + "sets only for natural r>=2 and rational 0<t<1/2 whose actual closed "
                    + "zero strip fails. One common dense G_delta G in (1,infinity) works "
                    + "for all r>=2 and all real 0<alpha<=1/2. If every actual nontrivial "
                    + "zero rho has re(rho)<=1-alpha, every q>1 has an eventual lower bound. "
                    + "Otherwise every q in G has arbitrarily negative samples after every "
                    + "cutoff. The index is exactly floor(q^k)^r, with the original strict "
                    + "record and exact N^alpha*log(N) weight.")),
                Paragraph(Text("A failing real alpha supplies an actual zero with "
                    + "re(rho)>1-alpha. Choose rational max(0,1-re(rho))<t<alpha. "
                    + "The exact identity A_alpha(j)=(j^r)^(alpha-t)*A_t(j), with factor "
                    + "at least one on j>=2, preserves a strict negative hit in the needed "
                    + "direction. This countable construction includes alpha=1/2 and "
                    + "requires no attained zero-abscissa supremum. Equality in the closed "
                    + "strip belongs to the lower-bound side. Neither this application "
                    + "nor the generic theorem proves RH, a fixed prescribed-base result, "
                    + "or a measure-almost-everywhere assertion."))),
            DescribeRole.Theorem))));
}
