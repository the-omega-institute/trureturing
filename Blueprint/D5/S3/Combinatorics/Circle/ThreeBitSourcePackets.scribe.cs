using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeBitSourcePacketsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact second packets preserve source masks while jointly bounding the two untouched ladders.",
        H("Exact packets for the two remaining ladders"),
        Blocks(
            Paragraph(Text("This internal module assembles the complementary coefficient regimes consumed by normalized_order in ThreeBitSource. Put P=2^x, Q=2^y and R=2^z, with 0<x, 0<y, 2<=z, x<=z and y<=z. The normalized bases are u=1+P+PQ, v=1+R+RP and w=1+Q+QR. The interface additionally uses u<=w and a legal first seam 0<=h<=C.")),
            Paragraph(Text("The exact source quotient is n=floor(R(P+1)/(2u)). Set C=(P/2)w-(u+1)/2, h=v-(n+1)u and D=(w-1)/2. second_packet supplies natural c,dV,dW with the binary support of c contained in that of n, dV<Q/2 and dW<P/2. For the single joint mass q=cu+dVv+dWw it proves q>=0 and 0<=C-h-q<=D. These same coefficients are later mapped to disjoint physical labels.")),
            Paragraph(Text("For P<Q, the power relation gives either Q>=4P or Q=2P. The first regime uses a ceiling choice on the V ladder. For Q=2P, the power R lies below P^2, equals P^2, or lies above it; the outer ranges are R<=P^2/2 and R>=2P^2. The middle construction uses P divisible by four, while P=2,R=4 is treated separately.")),
            Paragraph(Text("For P>=Q, write H=P/Q, delta=R-P-H+1 and T=(u-1)/2. When delta<=T, packet_direct takes c=n, dV=0 and dW=P/2-H, with final error T-delta. When delta>T, packet_exit transfers mass between both untouched ladders using a source-selected power r with (ru) mod w in [delta-T,w-u]. A proof that r is a present binary bit is supplied separately and is used to certify the support of n-r.")),
            Paragraph(Text("The Q=2 branch uses ThreeBitSourceQTwo. The ratios H=1,2,4 use source_top_bit after its actual hypothesis z>=y+2 has been established; the associated residue calculations have wrap counts zero, zero and one. The remaining cone uses ThreeBitSourceResidual. The resulting packet is consumed by the physical-label schedule in ThreeBitSource, whose single theorem Describe states the full source-order conclusion."))
        )));
}
