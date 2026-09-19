using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class CyclicStackPreimagesInvariantsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successful inputs have one low per high gap, ordered lows, and constrained high entries.",
        H("Cyclic-Stack Gap Invariants"),
        Blocks(
            Paragraph(Text(
                "A gapped word starts with a high entry and places at most one low entry after each "
                    + "high entry. Its high filter, low filter, and optional gap slots reconstruct "
                    + "the original word exactly.")),
            Paragraph(Text(
                "Any permutation whose cyclic-stack output is the layered target is gapped. Its "
                    + "low entries occur in increasing order, and the permutation condition fixes "
                    + "the low and high filters to their consecutive ranges. When all gaps through "
                    + "the last are filled, successful execution also forces the highs to increase.")))));
}
