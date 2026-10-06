using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCollisionColorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SevenCycleCollisionColors", H("SevenCycleCollisionColors"),
        Blocks(Paragraph(Text("The first phase admits common color one. The zero-label feeding point and the rival admit color two with zero error. For phases one through six, every terminal scalar between the two critical entry coordinates follows the same six original affine branches and lies strictly inside the corresponding expanded color interval.")))));
}
