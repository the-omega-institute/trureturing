using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.EqualLastTwo;

internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Physical equal-last-two source banks",
        H("The c=d bank reserve and literal physical realization"),
        Blocks(
            Paragraph(Text("The source uses the released PacketNormalForm chains and the actual centered values. For c=d=s, write x=2^a, y=2^b, t=2^s, N=xy t^2-1, D=1+y+yt, A=xD+1, B=t(1+x+xy)+1, L=t^2(1+x)+t+1, and M=tyt+D. The new bases are 2A, 2B-1, 2L-1-t, and 2M-D. The old and new rows are computed by one source and one literal fresh label; source totals and every natural prefix remain part of the endpoint.")),
            Paragraph(Text("For b>=s+2 set J=a-s-3 and m=2^J=x/(8t). The four X-positive banks are {J} union [J+3,a-1), {J+1}, {J+2} union [a-b-1,J), and [0,a-b-1). Their masses are x/2-7m, 2m, 5m-x/(2y), and x/(2y)-1. Packets are [X,U,V,W]: bank0 with X, U positives with bank1, V positives with bank2, and W positives with bank3. The first packet has exactly s old positive labels, so the ear is inserted immediately before X.")),
            Paragraph(Text("For b=s+1 and a>=s+4 set J=a-s-4 and m=2^J=x/(16t). The banks are {J} union [J+4,a-1), {J+1}, {J+3}, and {J+2} union [0,J). Their masses are x/2-15m, 2m, 8m, and 5m-1. The same physical packet order and literal cut s are used.")),
            Paragraph(Text("The two remaining unbounded offsets are retained as literal plans. At a=s+2 the order is [U,V,X,W], with X local positions 0 and 1 transferred to U and V and all later X positions retained by X; the ear is before X and the cut is 3s+1. At a=s+3 the order is [X,V,U,W], with X local positions 1 and 2 transferred to U and V, local position 0 and all later X positions retained by X; the ear is before X and the cut is s.")),
            Paragraph(Text("Every packet endpoint inequality is proved in doubled integer coordinates. For the large strip write y=4tv,x=8tvu,m=vu with u,v>=1. For the adjacent large strip write x=16tm with m>=1. Substitution t=t0+4,u=u0+1,v=v0+1 or m=m0+1 turns every seam and peak slack into a polynomial with nonnegative integer coefficients. The two adjacent offset plans use the same exact coefficient proof in the single unbounded variable t>=4. The old doubled cap is N-1 and the new doubled cap is 2N. Chain telescoping proves every doubled terminal equals successor minus modulus; no integer-division identity is assumed.")),
            Paragraph(Text("The common physical permutation, exact totals and both all-prefix OriginalOrder predicates are reconstructed from these packets. Unrestricted physical J and complete Circle C3.1 remain open."))),
        []));
}
