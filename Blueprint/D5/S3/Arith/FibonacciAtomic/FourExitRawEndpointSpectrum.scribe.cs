using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FourExitRawEndpointSpectrumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal four-exit right-comb trees and their coordinatewise endpoint menu.",
        H("Four-Exit Raw Endpoint Spectrum"),
        Blocks(
            Paragraph(Text(
                "A right comb has k active slots and one compensation slot. Its baseline uses B in "
                + "every active slot and R0 in the compensation slot. An exceptional member replaces "
                + "one active block by A, Y, H, or Z and uses the corresponding compensation block.")),
            Paragraph(Text(
                "The endpoint menu contains a vector with one zero and all other coordinates one "
                + "for the baseline and each Y, H, or Z member. It also contains, for each slot, three "
                + "vectors with zero at A, two at one of Y, H, or Z, and one elsewhere.")))));
}
