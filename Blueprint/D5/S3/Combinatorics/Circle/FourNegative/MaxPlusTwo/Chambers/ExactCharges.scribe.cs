using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers;
internal sealed class ExactChargesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact remaining physical charges",
        H("Three negative seams"),
        Blocks(Paragraph(Text("For the four-block masked word, charge has positive-chain bases zero, one, Z+1 and TZ+T+1. Summing the actual physical labels and the first three negative charges gives remaining charges A-1-v0, A-Z-1+v2 and A-(TZ+T+1)+v3+(Z+1)w. The equalities retain the selected masks rather than replacing the remaining charge by the conservative bound A."))), []));
}
