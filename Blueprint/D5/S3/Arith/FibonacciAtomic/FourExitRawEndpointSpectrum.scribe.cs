using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitRawEndpointSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal four-exit trees and a zero-to-two raw-cost obstruction.",
        H("Four-Exit Raw Endpoint Spectrum"),
        Blocks(
            Paragraph(Text(
                "A right comb has k active slots and one compensation slot. Its baseline uses B in "
                + "every active slot and R0 in the compensation slot. An exceptional member replaces "
                + "one active block by A, Y, H, or Z and uses the corresponding compensation block.")),
            Paragraph(Text(
                "The endpoint menu contains a vector with one zero and all other coordinates one "
                + "for the baseline and each Y, H, or Z member. It also contains, for each slot, three "
                + "vectors with zero at A, two at one of Y, H, or Z, and one elsewhere.")),
            Paragraph(Text(
                "For every slot and every globally correct history-dependent controller, a cost "
                + "of 8k + 16 on its A member forces a cost of at least 8k + 18 on one of its Y, H, "
                + "or Z members. Restricting the actual response tree to these four members preserves "
                + "the original controller's cost lower bound.")),
            Paragraph(Text(
                "An A-leaf query is either common to the four members or gives two sibling members "
                + "the same nonleaf reply. In the latter case, those two members must subsequently "
                + "separate. Their shared leaf labels agree, so at least one receives another nonleaf "
                + "reply before the response tree can reach singleton survivors.")))));

}
