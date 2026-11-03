using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail;
internal sealed class BoundaryWordsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three exceptional literal words", H("Paired source arithmetic"),
        Blocks(
            Paragraph(Text("The triples (a,b,c)=(2,5,3),(2,7,5),(2,6,3) use explicit permutations of all original labels. The respective fresh cuts are 13,19,14, and d=c+1 in all three cases.")),
            Paragraph(Text("Each word is checked against the two centered source rows with the original seed. Both full strips are verified directly, and the general actual-source and zero-period transport results then supply the complete order and every finite repeated prefix."))), []));
}
