using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.UpperBound;

internal sealed class ExactDecksUpperBoundIteratedOverlapBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Iterated infiltrations isolate their maximal-length ordinary shuffles.",
        H("IteratedOverlapBounds"),
        Blocks(
            Paragraph(Text(
                "This module lifts the binary infiltration identity to a finite list of factors. "
                + "It bounds every iterated overlap by the total factor length and identifies the "
                + "maximal-length filtered stratum exactly with the iterated ordinary shuffles, "
                + "retaining their list multiplicities.")))));

}
