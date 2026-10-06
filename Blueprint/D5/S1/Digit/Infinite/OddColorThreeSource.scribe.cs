using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class OddColorThreeSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd color words and actual periodic sources.",
        H("Odd color words and actual periodic sources"),
        Blocks(Paragraph(Text(
            "A positive odd window period excludes the alternating endpoint tails. "
            + "The signed-series fiber classification therefore separates the actual scalar "
            + "coordinates of distinct periodic addresses at every time.")))));
}
