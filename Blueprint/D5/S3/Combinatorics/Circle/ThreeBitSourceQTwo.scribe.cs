using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeBitSourceQTwoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The empty middle ladder is handled by exact source-forced bits and their full modular wrap counts.",
        H("The Q=2 empty-ladder boundary"),
        Blocks(
            Paragraph(Text("When Q=2, the V ladder has length zero and its legal natural coefficient is dV=0. This internal module supplies the selected-bit interface used by second_packet in ThreeBitSourcePackets. The P=2 empty-packet case is handled by that consumer before calling the results here.")),
            Paragraph(Text("For x>=2 and l>=2, set P=2^x, K=2^l and R=KP. The unused source mask is n=floor(KP(P+1)/(2(1+3P))). source_q_two_bits proves that bit l-2 is present. It also proves that bit l-1 is present when P mod 12=4, or that bit l is present when P mod 12=8. These are the two possible residue classes of the relevant power P.")),
            Paragraph(Text("With u=1+3P and w=3+2KP, q_two_selected_bit chooses an actual present bit e<=l for which (2^e u) mod w belongs to [KP-3P+1,w-u]. The proof keeps the low K=4 boundary and the two power-residue branches. The odd branch includes its double wrap in the exact centered-to-modular calculation.")),
            Paragraph(Text("The selected bit is passed to the two-ladder transfer and deleted from the same unused U mask. The required membership proof is retained through the binary-support calculation, so the coefficient bound and the physical support come from one source realization. The complete physical permutation and all natural-length prefix bounds are stated by three_bit_source_order in ThreeBitSource."))
        )));
}
