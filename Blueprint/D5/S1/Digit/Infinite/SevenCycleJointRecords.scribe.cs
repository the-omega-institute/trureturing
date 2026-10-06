using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleJointRecordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual records with common future errors", H("Actual records with common future errors"),
        Blocks(Paragraph(Text("The null-label feeding source shares the literal tail of the first "
            + "periodic source. Two records against the same rival use different first colors "
            + "and a fixed common pair of future error sequences, with a uniform positive margin.")))));
}
