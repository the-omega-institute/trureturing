using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative;
internal sealed class FourNegativeEventualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quarter-grid phases and physical four-chain masks",
        H("A common phase with quantitative margins"),
        Blocks(
            Paragraph(Text("For positive integer periods associated with dyadic bases h<=D<4h/3, the internal simultaneous_half_phase lemma produces an integer R representing four times a common phase. Each period D has an integer n>=1 satisfying (4n-2)D<R<4nD. Sorting the three periods and their dyadic exponents separates equal top scales, adjacent scales and a wide-scale case. In the wide case r>2p+q, clipping one q upper half to (r/2,r), and advancing to the following q interval if its tail is too short, yields an interval longer than p/2. The first p upper half meeting that interval supplies the common quarter-grid point. This proof uses integer division and strict interval arithmetic.")),
            Paragraph(Text("For independent a,b,c>=2, put x=2^a,y=2^b,z=2^c,P=xyz. The three periods are D_B=1+x+xy,D_L=z(1+x),D_M=yz, with bases xy,xz,yz. Their maximum is less than P/3. The selected R has both integer scaled margins at least one and gives 1<=n_B<z/2,1<=n_L<y/2,1<=n_M<x/2. At t=2^d>=8P, the ceiling q=ceil(tR/(4A)), A=P+D_B, has rounding loss 0<=4Aq-tR<4A. The rounded_phase_seam estimate proves the strict reserve and peak inequalities for all three troughs.")),
            Paragraph(Text("The physical positive chain offsets are 0,d,d+c,d+c+b and their lengths are d-1,c-1,b-1,a-1. The two U masks are t/2-q and q-1; the V masks are n_B-1 and z/2-n_B; the W masks are n_L-1 and y/2-n_L; the X masks are n_M-1 and x/2-n_M. Existing bounded bit decoding and mask complementation prove that each pair partitions its full physical interval. The four_mask_inventory proof retains all labels, interleaves the four separate negative labels, and proves a permutation of the complete range. The eventual_mask_certificate consumes the phase and rounding proofs to produce these natural masks and all three strict seam bounds.")),
            Paragraph(Text("These are proof components for the explicit eventual four-isolated-bit family. They do not assert an arbitrary-source Circle C3.1 solution, a numerical-period quotient, or the remaining range 2<=d<a+b+c+3."))), []));
}
