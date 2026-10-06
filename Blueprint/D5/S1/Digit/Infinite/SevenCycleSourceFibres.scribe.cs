using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCycleSourceFibresDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique seven-cycle address fibres.", H("Unique seven-cycle address fibres"),
        Blocks(Paragraph(Text("The two periodic sources have arbitrarily late pairs of zero bits. Every seam address is eventually alternating, so no shifted source is a seam address. The signed-series fibre classification therefore gives a unique actual address at each orbit scalar.")))));
}
