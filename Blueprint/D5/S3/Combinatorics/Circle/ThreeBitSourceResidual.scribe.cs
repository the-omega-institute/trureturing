using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeBitSourceResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact source quotient forces an unused bit in a bounded window and a jointly legal two-ladder transfer.",
        H("Source-forced residual windows"),
        Blocks(
            Paragraph(Text("This internal module supplies packet_residual to second_packet in ThreeBitSourcePackets. Its packet regime is y>=2 and y+3<=x, with arbitrary l>=0. Write P=2^x, Q=2^y, L=2^l, R=LPQ and u=1+P+PQ. Thus Q>=4 and P/Q>=8, while the wrap-free source window is derived from the exact quotient.")),
            Paragraph(Text("Let F=floor(PQ(P+1)/(2u)) and b0=F mod Q. Dividing P/2 by the odd number Q+1 gives P/2=d(Q+1)+s. Coprimality of this power of two with Q+1 makes s nonzero. quotient_digit proves F=dQ+s-c for c equal to zero or one, together with 1<=s-c<Q. Consequently residual_digit proves 0<b0<Q.")),
            Paragraph(Text("For n=floor(LPQ(P+1)/(2u)), the exact nested-division identity gives floor(n/L)=F. The nonzero digit b0 forces a present bit at l+e for some e<y; residual_window can choose the least such digit. With r=2^(l+e), this yields L<=r<=LQ/2. erase_bit proves that the binary support of n-r is exactly the support of n with that bit removed.")),
            Paragraph(Text("Put H=P/Q, v=1+R+RP, w=1+Q+QR, delta=R-P-H+1, T=(u-1)/2 and D=(w-1)/2. residual_bounds gives delta-T<ru<w-u, so S=ru needs no modular wrap. The capped quotient i=min(Q/2,floor((S+T)/delta)) satisfies 1<=i<=Q/2 and 0<=S+T-i delta<=D.")),
            Paragraph(Text("The coefficients c=n-r, dV=i-1 and dW=P/2-iH are legal simultaneously. packet_residual combines their bounds, the actual binary-support deletion and the identity C-h-(cu+dVv+dWw)=S+T-i delta. Its support witness and error bound are both consumed in the source-dependent physical schedule. The full all-three-bit endpoint and its original-source attribution belong to ThreeBitSource."))
        )));
}
