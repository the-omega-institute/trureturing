using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleCollisionRecordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SevenCycleCollisionRecords", H("SevenCycleCollisionRecords"),
        Blocks(Paragraph(Text("The literal periodic Boolean streams determine their scalar phases by the original three-bit deletion recurrence. The rival has least positive window period seven, and the two streams have the guard sequence zero, zero, zero, one, one, zero, zero.")))));
}
