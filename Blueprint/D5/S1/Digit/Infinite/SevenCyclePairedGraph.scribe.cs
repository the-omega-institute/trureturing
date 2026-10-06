using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Infinite;

internal sealed class SevenCyclePairedGraphDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original paired graph and actual returns.", H("Original paired graph and actual returns"),
        Blocks(Paragraph(Text("All original guard-typed pieces and all original all-containment edges remain in the paired graph. The unique address over each seven-cycle scalar forces every outgoing source label and successor singleton. Every vertex reachable from an orbit pair therefore lies on the same actual orbit. The entire returning component has periodic output prefixes for both projections and their ordered pairs. The zero-label feeding head cannot be reached from that component.")))));
}
