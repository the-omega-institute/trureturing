using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeSmallSameSignSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward physical placement of three same-sign SMALL occurrences",
        H("Pair-block placement with adjacent SMALL occurrences"),
        Blocks(
            Paragraph(Text("Use six times each source increment so that the rational scale N/3 introduces no integer division. A LARGE block with deficit d has pair values 2N-2*4^j*d and -2N-4*4^j*d. Starting from height h, its valleys are h+2d-2*4^j*d and its intermediate peaks are h+2N+2d-4*4^j*d. The original TwoSmallPlacement.paired_segment induction checks every physical step. Monotonicity reduces the strip bounds to the final valley, first peak, and the endpoint inequality 4^(start+len)*d<=N. If sixfold prefix heights are in [0,3N] and N=2C+1, integrality gives the sharp unscaled interval [0,C].")),
            Paragraph(Text("For the normalized one-block case D>=1, set H=4^D and N=8H-1. The three SMALL values in sixfold units are 2(H-1), 4(H-1) and 8(H-1), at physical positions 0,1,2. Use [1], the first D-1 complete LARGE pairs, then [0,2], then the final LARGE pair. Every physical position below 2D+3 occurs once, every prefix lies in [0,3N], the mass is zero, and deleting positions 0,1,2 leaves the consecutive forward LARGE range starting at position 3. The initial pair block is allowed to be empty.")),
            Paragraph(Text("For two nonempty blocks B,D>=1 let G=4^B, H=4^D, with positive deficits d,e,z<N satisfying 2d=N+e, 2Ge=N+z and 2Hz=N+d. The SMALL values at positions 0,1,2B+2 are N-d,N-e,N-z in sixfold units. Start at position 1. If e<=z, place the first B-1 Y pairs, insert position 0, then place the last Y pair. If z<e, place all B Y pairs before inserting position 0. In both cases the height before the Z block is d-z. Place its first D-1 pairs, then position 2B+2, then its final pair. The same word is a physical permutation, stays in [0,3N], has mass zero, and its LARGE filter is exactly the consecutive Y range followed by the consecutive Z range. Both equality and empty initial segments are included.")),
            Paragraph(Text("The complete native theorem additionally requires extraction of the three actual physical gaps, the placement for three nonempty LARGE blocks, and transport of the same witness through the native phase and sign-restoring rotation. Those statements are not asserted by this document. Full arbitrary-source Circle Conjecture 3.1 remains open. The source context is Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2, Conjecture 3.1, DOI 10.5070/C6.68671."))), []));
}
