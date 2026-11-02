using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm;
internal sealed class StructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Packets ending in negative physical labels",
        H("Physical labels and endpoint bounds"),
        Blocks(Paragraph(Text("Splitting a physical word at its negative labels preserves every occurrence. When the last label is negative, each resulting block consists of a positive packet followed by one negative label, and there is no tail packet. Empty packets are allowed.")), Paragraph(Text("A literal insertion inside a packet moves to its right endpoint by crossing only positive labels. This transport preserves the same old word and all natural prefix bounds; it imposes no symmetry on unequal negative weights. The source-complete packet equivalence and uniform mask allocation are distinct obligations. Unrestricted uniform allocation and full physical J remain open."))), []));
}
