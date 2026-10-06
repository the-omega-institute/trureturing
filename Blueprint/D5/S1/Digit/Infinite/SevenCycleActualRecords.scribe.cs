using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleActualRecordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict periodic error margins", H("Strict periodic error margins"),
        Blocks(Paragraph(Text("Every scalar strictly inside a budget-expanded color interval admits an interior target within strict error budget. A finite set of seven-phase targets supplies one positive common error margin for the two source streams.")))));
}
