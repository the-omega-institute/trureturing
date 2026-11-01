using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm;
internal sealed class TransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive packet symmetry and rightward ear transport",
        H("Physical labels and endpoint bounds"),
        Blocks(Paragraph(Text("A nonnegative packet can be reordered arbitrarily without changing its endpoint sum. Every intermediate height remains between its starting and ending heights. The same reasoning slides a positive ear right across a positive interval: the two local paths have identical endpoints, and the old physical word stays fixed.")), Paragraph(Text("For a valid old zero-sum word, a final positive step contradicts nonnegativity of the preceding prefix. An ear after all old labels exposes the enlarged old-label total -A, so it cannot be legal when A>0. These are the two boundary exclusions needed for four slots rather than a fifth tail slot."))), []));
}
