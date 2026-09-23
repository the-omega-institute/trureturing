using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Patterns;

internal sealed class CyclicStackPreimagesFinalLowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A successful gapped input ending in a low entry has the complete increasing high range.",
        H("The Final-Low Invariant"),
        Blocks(
            Paragraph(Text(
                "While a low entry remains in the input, every successful run preserves the "
                    + "chronological order forced on the high entries. If the gapped input ends "
                    + "with a low entry, the residual stack exposes the reversed high sequence.")),
            Paragraph(Text(
                "Filtering the target and using permutation preservation then identifies the high "
                    + "entries with the complete consecutive high range. The same range conclusion "
                    + "follows from pairwise increasing highs, and the auxiliary assembly and "
                    + "length facts connect this invariant to the explicit candidates.")))));
}
