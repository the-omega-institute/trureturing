using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class CyclicHyperbolicSectorSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite forward chains and folded distance bounds in actual hyperbolic sectors.",
        H("Finite paths through complete sector seams"),
        Blocks(
            Paragraph(Text("Let I be any index type, next:I->I any successor map, and alpha(i) widths strictly between zero and pi. The piece at i is the actual closed sector S(alpha(i)) in the original hyperbolic three-space. Its complete upper face is identified with the complete lower face at next(i) by rotation through -alpha(i). The axis belongs to every face. Write C(r,z,t) for cylindricalPoint, and W(i,m)=sum over k<m of alpha(next^k(i)).")),
            Describe.Remark(
                DescribeId.Create("sector-finite-forward-run"),
                DeclarationHandle.Create("D5/S3/Geometry/Hyperideal/CyclicHyperbolicSectorSupport.short_angle_forward_run"),
                H("An original chain along a finite forward run"),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural m, starting tag i, positive radii r and R, arbitrary axial coordinates z and w, and local angles t in [0,alpha(i)] and u in [0,alpha(next^m(i))], suppose W(i,m)+u-t<pi. There is a literal original finite Chain from the tagged point (i,C(r,z,t)) to (next^m(i),C(R,w,u)) whose cost is ofReal(dist(C(r,z,t),C(R,w,W(i,m)+u))). No injectivity or periodicity of next is assumed.")),
                    Paragraph(Text("The construction inducts on m. A strict wall crossing lies on the developed hyperbolic segment, has positive transverse radius, and splits its distance exactly. Rotating the crossing onto the next lower face leaves the remaining distance unchanged. A closed-wall endpoint itself supplies the crossing. Appending the paid initial move, the actual zero-cost seam move and the inductively constructed tail gives the required original Chain.")),
                    Paragraph(Text("The same complete seams preserve the endpoint-dependent fold C(r,z,min(pi,norm([offset(i)+t-reference] in AddCircle(A)))). If offset(i)+alpha(i) and offset(next(i)) represent the same scalar class, this fold is nonexpanding in each piece and agrees on every seam, including axis points. Induction on all original Chain constructors and the unrestricted cost infimum gives fold_distance_lower. These finite-run and lower-bound statements supply the two comparisons for cyclic_sector_metric.")))))));
}
