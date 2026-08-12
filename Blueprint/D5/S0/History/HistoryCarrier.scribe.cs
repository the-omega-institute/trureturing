using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History;

internal sealed class HistoryCarrierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite marker and event histories preserve the source append direction and low-level encoding.",
        H("History Carrier"),
        Blocks(
            Paragraph(
                Text("Marker histories form the free monoid on exactly two constructors. Because source expressions extend at the left edge, source append is represented by reversed free-monoid multiplication; its recursive equation and both unit laws follow definitionally from this orientation.")),
            Paragraph(
                Text("Events carry source history, opcode, input code, and output marker. Event histories embed into marker histories with the literal low-level code `0 -> 00`, `1 -> 01`, and separator `11`; the bridge preserves appending one generated event.")),
            Paragraph(
                Ref("D5/S0/History/HistoryCarrier"),
                Text(" exposes `marker_splice_laws`, which packages associativity and both identity laws as the atomic acceptance theorem. The prime-power Godel numbering and its decoder round-trip are explicitly outside this producer cluster and tracked separately.")))));
}
