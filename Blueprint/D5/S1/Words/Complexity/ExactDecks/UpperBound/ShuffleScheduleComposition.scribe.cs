using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ExactDecks.UpperBound;

internal sealed class ExactDecksUpperBoundShuffleScheduleCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary schedules compose into valid indexed schedules for all factors.",
        H("ShuffleScheduleComposition"),
        Blocks(
            Paragraph(Text(
                "This module privately composes a binary shuffle of the first factor with an "
                + "indexed schedule for the remaining factors. The resulting schedule preserves "
                + "every source occurrence, evaluates to the same interleaved word, and supplies "
                + "the schedule witness for each iterated ordinary shuffle.")))));

}
