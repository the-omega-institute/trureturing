using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCollisionDataDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seven-phase source coordinates.", H("Seven-phase source coordinates"),
        Blocks(Paragraph(Text("The observation radius is lambda minus g^7*(g-1/5)/(4*(1+g^7)). "
            + "The two actual source streams repeat 3,3,5,5,3,2,2 and 0,3,5,5,3,2,2. "
            + "Their guards are 0,0,0,1,1,0,0, and their common suffix uses the original branch maps.")))));
}
