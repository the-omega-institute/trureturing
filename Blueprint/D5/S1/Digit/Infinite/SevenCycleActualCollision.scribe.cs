using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleActualCollisionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual persistent entry collision", H("Actual persistent entry collision"),
        Blocks(Paragraph(Text("Strict actual records against the same rival supply the permitted "
            + "colors at both entries and at every future phase. Their common literal first "
            + "tail survives each recursively defined finite horizon.")))));
}
